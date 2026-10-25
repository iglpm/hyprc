//! Compiling one function instance from MIR to x86-64.
//!
//! Every local lives in a stack slot; each statement loads what it needs into scratch
//! registers, computes, and stores. That is the code an unoptimized build gets anyway, and it
//! comes out of a single pass over the MIR.
//!
//! Register discipline: destination places are addressed through r11 (r10 holds a wide
//! pointer's metadata, r9 is scratch); source places through rsi (rdi metadata, r8
//! scratch); arithmetic uses rax, rcx, rdx and xmm0/xmm1. Call arguments are first copied to
//! frame temporaries, then loaded into the argument registers all at once.

use super::abi::{PassMode, RegClass, classify_c, classify_rust};
use super::asm::*;
use crate::CodegenCx;
use hyprc_hir::DefKind;
use hyprc_mir::layout::{Abi, Layout, TagEncoding, Variants};
use hyprc_mir::mir::*;
use hyprc_mir::mono::{Instance, InstanceKind};
use hyprc_ty::{Abi as FnAbi, Ty, TyKind};
use std::sync::Arc;

#[derive(Clone, Copy, Debug)]
enum Loc {
    Stack(i32),
    /// The return place when it's the caller's memory: the pointer is in this slot.
    Indirect(i32),
    Zst,
}

#[derive(Clone, Copy, Debug)]
enum Base {
    Rbp,
    Reg(Reg),
}

/// A place: its address (`base + disp`), type and layout, and for unsized places the
/// metadata (in a register).
#[derive(Clone, Debug)]
struct PlaceRef {
    base: Base,
    disp: i32,
    ty: Ty,
    layout: Arc<Layout>,
    meta: Option<Reg>,
}

impl PlaceRef {
    fn mem(&self, extra: i32) -> Mem {
        let base = match self.base {
            Base::Rbp => Reg::Rbp,
            Base::Reg(r) => r,
        };
        mem(base, self.disp + extra)
    }
}

/// Which registers a place computation may use.
#[derive(Clone, Copy)]
struct Regs {
    addr: Reg,
    meta: Reg,
    scratch: Reg,
}

const DEST: Regs = Regs {
    addr: Reg::R11,
    meta: Reg::R10,
    scratch: Reg::R9,
};
const SRC: Regs = Regs {
    addr: Reg::Rsi,
    meta: Reg::Rdi,
    scratch: Reg::R8,
};

const GPR_ARGS: [Reg; 6] = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];

pub struct CompiledFn {
    pub symbol: String,
    pub code: Vec<u8>,
    pub relocs: Vec<Reloc>,
    pub global: bool,
}

pub(crate) struct FnGen<'c, 'a, 'h> {
    cx: &'c CodegenCx<'a, 'h>,
    inst: Instance,
    body: Arc<Body>,
    a: Asm,
    loc: Vec<Loc>,
    tys: Vec<Ty>,
    labels: Vec<Label>,
    frame: i32,
    frame_patch: usize,
    max_outgoing: u32,
    ret_mode: PassMode,
    c_abi: bool,
}

fn align_up(x: i32, a: i32) -> i32 {
    (x + a - 1) / a * a
}

impl<'c, 'a, 'h> FnGen<'c, 'a, 'h> {
    pub(crate) fn new(cx: &'c CodegenCx<'a, 'h>, inst: Instance, body: Arc<Body>) -> Self {
        FnGen {
            cx,
            inst,
            body,
            a: Asm::new(),
            loc: Vec::new(),
            tys: Vec::new(),
            labels: Vec::new(),
            frame: 0,
            frame_patch: 0,
            max_outgoing: 0,
            ret_mode: PassMode::Ignore,
            c_abi: false,
        }
    }

    fn mono(&self, t: Ty) -> Ty {
        hyprc_mir::monomorphize(self.cx.tcx, self.inst.args, t)
    }

    fn layout(&self, t: Ty) -> Result<Arc<Layout>, String> {
        self.cx
            .lcx
            .layout_of(t)
            .map_err(|e| format!("can't lay out `{t}`: {e:?}"))
    }

    fn alloc(&mut self, size: u64, align: u64) -> i32 {
        let align = align.clamp(1, 16) as i32;
        self.frame = align_up(self.frame + size.max(1) as i32, align);
        -self.frame
    }

    fn classify(&self, l: &Arc<Layout>) -> PassMode {
        if self.c_abi {
            classify_c(l)
        } else {
            classify_rust(l)
        }
    }

    // ---------------------------------------------------------------------------------------
    // The function

    pub(crate) fn compile(mut self) -> Result<CompiledFn, String> {
        let body = self.body.clone();
        let symbol = self.cx.symbol_for(self.inst);
        let global = self.cx.is_exported(self.inst);
        self.c_abi = self.cx.instance_abi(self.inst) == FnAbi::C;
        for l in &body.locals {
            let t = self.mono(l.ty);
            self.tys.push(t);
        }
        // Prologue; the frame size is patched in at the end.
        self.a.push(Reg::Rbp);
        self.a.mov_rr(Size::B64, Reg::Rbp, Reg::Rsp);
        self.a
            .alu_ri(Alu::Sub, Size::B64, Reg::Rsp, 0x7fff_fff0u32 as i32);
        self.frame_patch = self.a.code.len() - 4;
        // Slots.
        let ret_layout = self.layout(self.tys[0])?;
        self.ret_mode = self.classify(&ret_layout);
        if self.ret_mode == PassMode::Stack {
            self.ret_mode = PassMode::Indirect;
        }
        for (i, &t) in self.tys.clone().iter().enumerate() {
            let l = self.layout(t)?;
            let loc = if i == 0 && self.ret_mode == PassMode::Indirect {
                let slot = self.alloc(8, 8);
                Loc::Indirect(slot)
            } else if l.size == 0 {
                Loc::Zst
            } else {
                Loc::Stack(self.alloc(l.size, l.align))
            };
            self.loc.push(loc);
        }
        // Incoming arguments.
        let mut gpr = 0usize;
        let mut xmm = 0u8;
        let mut stack_off = 16i32;
        if let Loc::Indirect(slot) = self.loc[0] {
            self.a.store(Size::B64, mem(Reg::Rbp, slot), GPR_ARGS[0]);
            gpr = 1;
        }
        for i in 1..=body.arg_count {
            let t = self.tys[i];
            let l = self.layout(t)?;
            let mode = self.classify(&l);
            let Loc::Stack(off) = self.loc[i] else {
                continue;
            };
            match mode {
                PassMode::Ignore => {}
                PassMode::Direct(classes) => {
                    let needed_gpr = classes.iter().filter(|c| **c == RegClass::Int).count();
                    let needed_xmm = classes.len() - needed_gpr;
                    if gpr + needed_gpr > 6 || xmm as usize + needed_xmm > 8 {
                        // Spilled to the stack.
                        self.copy_mem(mem(Reg::Rbp, off), mem(Reg::Rbp, stack_off), l.size);
                        stack_off += align_up(l.size as i32, 8);
                        continue;
                    }
                    for (k, c) in classes.iter().enumerate() {
                        let (piece_off, piece_size) = self.eightbyte(&l, k, classes.len());
                        match c {
                            RegClass::Int => {
                                self.store_sized(
                                    mem(Reg::Rbp, off + piece_off),
                                    GPR_ARGS[gpr],
                                    piece_size,
                                );
                                gpr += 1;
                            }
                            RegClass::Sse => {
                                self.a.store_f(
                                    piece_size == 8,
                                    mem(Reg::Rbp, off + piece_off),
                                    Xmm(xmm),
                                );
                                xmm += 1;
                            }
                        }
                    }
                }
                PassMode::Indirect => {
                    let src = if gpr < 6 {
                        let r = GPR_ARGS[gpr];
                        gpr += 1;
                        r
                    } else {
                        self.a.load(Size::B64, Reg::Rax, mem(Reg::Rbp, stack_off));
                        stack_off += 8;
                        Reg::Rax
                    };
                    self.a.mov_rr(Size::B64, Reg::Rsi, src);
                    self.copy_mem(mem(Reg::Rbp, off), mem(Reg::Rsi, 0), l.size);
                }
                PassMode::Stack => {
                    self.copy_mem(mem(Reg::Rbp, off), mem(Reg::Rbp, stack_off), l.size);
                    stack_off += align_up(l.size as i32, 8);
                }
            }
        }
        // Blocks.
        self.labels = (0..body.blocks.len()).map(|_| self.a.new_label()).collect();
        for (i, bb) in body.blocks.iter().enumerate() {
            let label = self.labels[i];
            self.a.bind(label);
            for s in &bb.stmts {
                self.statement(s)?;
            }
            if let Some(t) = &bb.terminator {
                self.terminator(t)?;
            } else {
                self.a.ud2();
            }
        }
        self.a.finish();
        let frame = align_up(self.frame + self.max_outgoing as i32, 16);
        self.a.code[self.frame_patch..self.frame_patch + 4].copy_from_slice(&frame.to_le_bytes());
        Ok(CompiledFn {
            symbol,
            code: self.a.code,
            relocs: self.a.relocs,
            global,
        })
    }

    /// The offset and size of the `k`-th of `n` register pieces of a value passed in
    /// registers. A scalar pair in two registers has one scalar in each, even when both fit
    /// one eightbyte (hyprc's Rust convention).
    fn eightbyte(&self, l: &Arc<Layout>, k: usize, n: usize) -> (i32, u64) {
        match l.abi {
            Abi::ScalarPair(a, b) if n == 2 => {
                if k == 0 {
                    (0, a.prim.size(8))
                } else {
                    (l.pair_b_offset(8) as i32, b.prim.size(8))
                }
            }
            Abi::Scalar(s) => (k as i32 * 8, s.prim.size(8).min(8)),
            _ => {
                let off = k as u64 * 8;
                (off as i32, (l.size - off).min(8))
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    // Memory helpers

    fn store_sized(&mut self, m: Mem, r: Reg, size: u64) {
        match size {
            0 => {}
            1 => self.a.store(Size::B8, m, r),
            2 => self.a.store(Size::B16, m, r),
            4 => self.a.store(Size::B32, m, r),
            8 => self.a.store(Size::B64, m, r),
            3 | 5 | 6 | 7 => {
                // Odd sizes (packed pairs): byte by byte from a copy.
                self.a.mov_rr(Size::B64, Reg::Rcx, r);
                for i in 0..size as i32 {
                    self.a.store(
                        Size::B8,
                        Mem {
                            disp: m.disp + i,
                            ..m
                        },
                        Reg::Rcx,
                    );
                    self.a.shift_ri(Shift::Shr, Size::B64, Reg::Rcx, 8);
                }
            }
            _ => self.a.store(Size::B64, m, r),
        }
    }

    fn load_sized(&mut self, r: Reg, m: Mem, size: u64) {
        match size {
            1 => self.a.load_zx(Size::B8, r, m),
            2 => self.a.load_zx(Size::B16, r, m),
            4 => self.a.load(Size::B32, r, m),
            _ => self.a.load(Size::B64, r, m),
        }
    }

    /// Copies `size` bytes; clobbers rax (and rcx/rsi/rdi for large copies).
    fn copy_mem(&mut self, dst: Mem, src: Mem, size: u64) {
        if size > 128 {
            self.a.lea(Reg::Rax, src);
            self.a.push(Reg::Rsi);
            self.a.push(Reg::Rdi);
            self.a.lea(
                Reg::Rdi,
                Mem {
                    disp: dst.disp + if dst.base == Reg::Rsp { 16 } else { 0 },
                    ..dst
                },
            );
            self.a.mov_rr(Size::B64, Reg::Rsi, Reg::Rax);
            self.a.mov_ri(Reg::Rcx, size);
            self.a.rep_movsb();
            self.a.pop(Reg::Rdi);
            self.a.pop(Reg::Rsi);
            return;
        }
        let mut off = 0i32;
        let mut left = size;
        for (chunk, s) in [
            (8u64, Size::B64),
            (4, Size::B32),
            (2, Size::B16),
            (1, Size::B8),
        ] {
            while left >= chunk {
                self.a.load(
                    s,
                    Reg::Rax,
                    Mem {
                        disp: src.disp + off,
                        ..src
                    },
                );
                self.a.store(
                    s,
                    Mem {
                        disp: dst.disp + off,
                        ..dst
                    },
                    Reg::Rax,
                );
                off += chunk as i32;
                left -= chunk;
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    // Places

    fn place(&mut self, p: &Place, regs: Regs) -> Result<PlaceRef, String> {
        let ty = self.tys[p.local.index()];
        let layout = self.layout(ty)?;
        let mut pr = match self.loc[p.local.index()] {
            Loc::Stack(off) => PlaceRef {
                base: Base::Rbp,
                disp: off,
                ty,
                layout,
                meta: None,
            },
            Loc::Zst => PlaceRef {
                base: Base::Rbp,
                disp: 0,
                ty,
                layout,
                meta: None,
            },
            Loc::Indirect(slot) => {
                self.a.load(Size::B64, regs.addr, mem(Reg::Rbp, slot));
                PlaceRef {
                    base: Base::Reg(regs.addr),
                    disp: 0,
                    ty,
                    layout,
                    meta: None,
                }
            }
        };
        let mut downcast: Option<u32> = None;
        for e in &p.projection {
            match e {
                PlaceElem::Deref => {
                    let pointee = match *pr.ty.kind() {
                        TyKind::Ref(t, _) | TyKind::RawPtr(t, _) => t,
                        TyKind::Adt(_, args) => args.ty(0),
                        _ => return Err(format!("deref of `{}`", pr.ty)),
                    };
                    let pl = self.layout(pointee)?;
                    let fat = self.cx.lcx.pointee_metadata(pointee).is_some();
                    if fat {
                        self.a.load(Size::B64, regs.meta, pr.mem(8));
                    }
                    self.a.load(Size::B64, regs.addr, pr.mem(0));
                    pr = PlaceRef {
                        base: Base::Reg(regs.addr),
                        disp: 0,
                        ty: pointee,
                        layout: pl,
                        meta: if fat { Some(regs.meta) } else { None },
                    };
                    downcast = None;
                }
                PlaceElem::Field(i, fty) => {
                    let fty = self.mono(*fty);
                    let container = match downcast {
                        Some(v) => self.cx.lcx.variant_layout(&pr.layout, v),
                        None => pr.layout.clone(),
                    };
                    let off = container.field_offset(*i as usize) as i32;
                    let fl = self.layout(fty)?;
                    pr = PlaceRef {
                        base: pr.base,
                        disp: pr.disp + off,
                        ty: fty,
                        layout: fl,
                        meta: pr.meta,
                    };
                    downcast = None;
                }
                PlaceElem::Downcast(v) => downcast = Some(*v),
                PlaceElem::Index(idx) => {
                    let elem = pr
                        .ty
                        .builtin_index()
                        .ok_or_else(|| format!("index into `{}`", pr.ty))?;
                    let el = self.layout(elem)?;
                    self.make_reg_based(&mut pr, regs);
                    let Loc::Stack(ioff) = self.loc[idx.index()] else {
                        return Err("index local without a slot".into());
                    };
                    self.a.load(Size::B64, regs.scratch, mem(Reg::Rbp, ioff));
                    let stride = el.size.next_multiple_of(el.align) as i32;
                    if stride != 1 {
                        self.mul_imm(regs.scratch, stride);
                    }
                    self.a.alu_rr(Alu::Add, Size::B64, regs.addr, regs.scratch);
                    pr = PlaceRef {
                        base: pr.base,
                        disp: pr.disp,
                        ty: elem,
                        layout: el,
                        meta: None,
                    };
                }
                PlaceElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let elem = pr
                        .ty
                        .builtin_index()
                        .ok_or_else(|| format!("index into `{}`", pr.ty))?;
                    let el = self.layout(elem)?;
                    let stride = el.size.next_multiple_of(el.align) as i32;
                    if *from_end {
                        // `len - offset`
                        let Some(meta) = pr.meta else {
                            return Err("from-end index without a length".into());
                        };
                        self.make_reg_based(&mut pr, regs);
                        self.a.mov_rr(Size::B64, regs.scratch, meta);
                        self.a
                            .alu_ri(Alu::Sub, Size::B64, regs.scratch, *offset as i32);
                        if stride != 1 {
                            self.mul_imm(regs.scratch, stride);
                        }
                        self.a.alu_rr(Alu::Add, Size::B64, regs.addr, regs.scratch);
                    } else {
                        pr.disp += *offset as i32 * stride;
                    }
                    pr = PlaceRef {
                        base: pr.base,
                        disp: pr.disp,
                        ty: elem,
                        layout: el,
                        meta: None,
                    };
                }
                PlaceElem::Subslice { from, to, from_end } => {
                    let elem = pr
                        .ty
                        .builtin_index()
                        .ok_or_else(|| format!("subslice of `{}`", pr.ty))?;
                    let el = self.layout(elem)?;
                    let stride = el.size.next_multiple_of(el.align) as i32;
                    pr.disp += *from as i32 * stride;
                    if *from_end {
                        if let Some(meta) = pr.meta {
                            self.a
                                .alu_ri(Alu::Sub, Size::B64, meta, (*from + *to) as i32);
                        }
                        let t = Ty::slice(elem);
                        let l = self.layout(t)?;
                        pr = PlaceRef {
                            ty: t,
                            layout: l,
                            ..pr
                        };
                    } else {
                        let t = hyprc_mir::mono::projection_ty(self.cx.tcx, pr.ty, e);
                        let l = self.layout(t)?;
                        pr = PlaceRef {
                            ty: t,
                            layout: l,
                            ..pr
                        };
                    }
                }
            }
        }
        if let Some(v) = downcast {
            pr.layout = self.cx.lcx.variant_layout(&pr.layout, v);
        }
        Ok(pr)
    }

    fn make_reg_based(&mut self, pr: &mut PlaceRef, regs: Regs) {
        match pr.base {
            Base::Rbp => {
                self.a.lea(regs.addr, mem(Reg::Rbp, pr.disp));
                pr.base = Base::Reg(regs.addr);
                pr.disp = 0;
            }
            Base::Reg(r) => {
                if pr.disp != 0 || r != regs.addr {
                    self.a.lea(regs.addr, pr.mem(0));
                    pr.base = Base::Reg(regs.addr);
                    pr.disp = 0;
                }
            }
        }
    }

    /// `r *= imm` without touching other registers.
    fn mul_imm(&mut self, r: Reg, imm: i32) {
        if imm.count_ones() == 1 {
            self.a
                .shift_ri(Shift::Shl, Size::B64, r, imm.trailing_zeros() as u8);
        } else {
            self.a.imul_rri(r, r, imm);
        }
    }

    // ---------------------------------------------------------------------------------------
    // Operands

    fn operand_ty(&self, op: &Operand) -> Ty {
        match op {
            Operand::Constant(c) => self.mono(c.ty),
            Operand::Copy(p) | Operand::Move(p) => {
                self.mono(hyprc_mir::mono::place_ty(self.cx.tcx, &self.body, p))
            }
        }
    }

    /// Stores an operand's value at `dst` (whose type matches).
    fn store_operand(&mut self, dst: Mem, op: &Operand, size: u64) -> Result<(), String> {
        if size == 0 {
            return Ok(());
        }
        match op {
            Operand::Copy(p) | Operand::Move(p) => {
                // Save the destination base across the source computation if needed.
                let src = self.place(p, SRC)?;
                let size = size.min(src.layout.size.max(size));
                self.copy_mem(dst, src.mem(0), size);
            }
            Operand::Constant(c) => self.store_constant(dst, c, size)?,
        }
        Ok(())
    }

    fn store_constant(&mut self, dst: Mem, c: &Constant, size: u64) -> Result<(), String> {
        let ty = self.mono(c.ty);
        match &c.kind {
            ConstValue::ZeroSized => {}
            ConstValue::Scalar(v) => self.store_imm(dst, *v, size),
            ConstValue::Bytes(bytes) => {
                let sym = self.cx.rodata_symbol(bytes);
                self.a.lea_rip(Reg::Rax, &sym, 0);
                self.a.store(Size::B64, dst, Reg::Rax);
                // `&str`, `&[u8]`: the length too. `&[u8; N]` is thin.
                if size >= 16 {
                    self.a.mov_ri(Reg::Rax, bytes.len() as u64 - if matches!(ty.kind(), TyKind::Ref(t, _) if matches!(t.kind(), TyKind::Adt(..))) { 1 } else { 0 });
                    self.a.store(
                        Size::B64,
                        Mem {
                            disp: dst.disp + 8,
                            ..dst
                        },
                        Reg::Rax,
                    );
                }
            }
            ConstValue::StaticRef(d) => {
                let sym = self.cx.static_symbol(*d);
                self.a.lea_rip(Reg::Rax, &sym, 0);
                self.a.store(Size::B64, dst, Reg::Rax);
            }
            ConstValue::Item(d, args) => {
                let args = args.subst(self.inst.args);
                // A trait's associated constant: the impl's value.
                let (d, args) = match self.cx.resolve(*d, args) {
                    Some(Instance {
                        kind: InstanceKind::Item(m),
                        args,
                    }) => (m, args),
                    _ => (*d, args),
                };
                let v = self.cx.eval_const_item(d, args, ty)?;
                self.store_imm(dst, v, size);
            }
            ConstValue::Unevaluated(k) => {
                let k = k.subst(self.inst.args);
                let v = self.cx.eval_const(k)?;
                self.store_imm(dst, v, size);
            }
        }
        Ok(())
    }

    fn store_imm(&mut self, dst: Mem, v: u128, size: u64) {
        let mut off = 0i32;
        let mut left = size;
        let mut val = v;
        while left > 0 {
            let chunk = if left >= 8 {
                8
            } else if left >= 4 {
                4
            } else if left >= 2 {
                2
            } else {
                1
            };
            let piece = (val
                & if chunk == 8 {
                    u64::MAX as u128
                } else {
                    (1u128 << (chunk * 8)) - 1
                }) as u64;
            let m = Mem {
                disp: dst.disp + off,
                ..dst
            };
            if chunk == 8 && !(piece as i64 >= i32::MIN as i64 && piece as i64 <= i32::MAX as i64) {
                self.a.mov_ri(Reg::Rax, piece);
                self.a.store(Size::B64, m, Reg::Rax);
            } else {
                self.a.store_imm(Size::from_bytes(chunk), m, piece as i32);
            }
            off += chunk as i32;
            left -= chunk;
            val = if chunk >= 16 { 0 } else { val >> (chunk * 8) };
        }
    }

    /// Loads a scalar operand (≤ 8 bytes) into a register, extended to 64 bits by the
    /// type's signedness.
    fn load_scalar(&mut self, op: &Operand, r: Reg) -> Result<Ty, String> {
        let ty = self.operand_ty(op);
        let size = self.layout(ty)?.size;
        let signed = ty.is_signed();
        match op {
            Operand::Constant(c) => match &c.kind {
                ConstValue::Scalar(v) => {
                    let v = if signed {
                        hyprc_ty::consteval::sext(*v, ty, self.cx.tcx.pointer_width) as u64
                    } else {
                        *v as u64
                    };
                    self.a.mov_ri(r, v);
                }
                ConstValue::ZeroSized => self.a.mov_ri(r, 0),
                _ => {
                    let slot = self.alloc(size.max(8), 8);
                    self.store_constant(mem(Reg::Rbp, slot), c, size)?;
                    self.load_ext(r, mem(Reg::Rbp, slot), size, signed);
                }
            },
            Operand::Copy(p) | Operand::Move(p) => {
                let src = self.place(p, SRC)?;
                self.load_ext(r, src.mem(0), size, signed);
            }
        }
        Ok(ty)
    }

    fn load_ext(&mut self, r: Reg, m: Mem, size: u64, signed: bool) {
        match (size, signed) {
            (0, _) => self.a.mov_ri(r, 0),
            (1, false) => self.a.load_zx(Size::B8, r, m),
            (2, false) => self.a.load_zx(Size::B16, r, m),
            (4, false) => self.a.load(Size::B32, r, m),
            (1, true) => self.a.load_sx(Size::B8, r, m),
            (2, true) => self.a.load_sx(Size::B16, r, m),
            (4, true) => self.a.load_sx(Size::B32, r, m),
            _ => self.a.load(Size::B64, r, m),
        }
    }

    fn load_float(&mut self, op: &Operand, x: Xmm) -> Result<bool, String> {
        let ty = self.operand_ty(op);
        let double = matches!(ty.kind(), TyKind::Float(hyprc_hir::FloatTy::F64));
        match op {
            Operand::Constant(c) => {
                let ConstValue::Scalar(v) = c.kind else {
                    return Err("non-scalar float constant".into());
                };
                self.a.mov_ri(Reg::Rax, v as u64);
                self.a.movq_to_xmm(double, x, Reg::Rax);
            }
            Operand::Copy(p) | Operand::Move(p) => {
                let src = self.place(p, SRC)?;
                self.a.load_f(double, x, src.mem(0));
            }
        }
        Ok(double)
    }

    // ---------------------------------------------------------------------------------------
    // Statements

    fn statement(&mut self, s: &Statement) -> Result<(), String> {
        match &s.kind {
            StatementKind::Assign(p, rv) => self.assign(p, rv),
            StatementKind::SetDiscriminant(p, v) => {
                let d = self.place(p, DEST)?;
                self.write_tag(&d, *v)
            }
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {
                Ok(())
            }
        }
    }

    /// Stores rax (and rdx for pairs) to a destination place, by size.
    fn store_result(&mut self, p: &Place, size: u64) -> Result<(), String> {
        let d = self.place(p, DEST)?;
        self.store_sized(d.mem(0), Reg::Rax, size.min(8));
        Ok(())
    }

    fn assign(&mut self, p: &Place, rv: &Rvalue) -> Result<(), String> {
        let dty = self.mono(hyprc_mir::mono::place_ty(self.cx.tcx, &self.body, p));
        let dl = self.layout(dty)?;
        if dl.size == 0 && !matches!(rv, Rvalue::Aggregate(..)) {
            return Ok(());
        }
        match rv {
            Rvalue::Use(op) => {
                // Source first (rsi), then the destination (r11): both stay live for the copy.
                match op {
                    Operand::Copy(sp) | Operand::Move(sp) => {
                        let src = self.place(sp, SRC)?;
                        let d = self.place(p, DEST)?;
                        self.copy_mem(d.mem(0), src.mem(0), dl.size);
                    }
                    Operand::Constant(c) => {
                        let d = self.place(p, DEST)?;
                        self.store_constant(d.mem(0), c, dl.size)?;
                    }
                }
                Ok(())
            }
            Rvalue::BinaryOp(op, a, b) => self.binary(p, *op, a, b, dl.size, false),
            Rvalue::CheckedBinaryOp(op, a, b) => self.binary(p, *op, a, b, dl.size, true),
            Rvalue::UnaryOp(op, a) => self.unary(p, *op, a, dty),
            Rvalue::Cast(kind, a, to) => self.cast(p, *kind, a, self.mono(*to)),
            Rvalue::Ref(_, sp) | Rvalue::RawPtr(_, sp) => {
                let src = self.place(sp, SRC)?;
                self.a.lea(Reg::Rax, src.mem(0));
                if let Some(meta) = src.meta {
                    self.a.mov_rr(Size::B64, Reg::Rdx, meta);
                }
                let d = self.place(p, DEST)?;
                self.a.store(Size::B64, d.mem(0), Reg::Rax);
                if src.meta.is_some() {
                    self.a.store(Size::B64, d.mem(8), Reg::Rdx);
                }
                Ok(())
            }
            Rvalue::Len(sp) => {
                let src = self.place(sp, SRC)?;
                match (*src.ty.kind(), src.meta) {
                    (TyKind::Array(_, n), _) => {
                        let n = self.cx.eval_const(n)?;
                        self.a.mov_ri(Reg::Rax, n as u64);
                    }
                    (_, Some(meta)) => self.a.mov_rr(Size::B64, Reg::Rax, meta),
                    _ => return Err("length of a place without one".into()),
                }
                self.store_result(p, 8)
            }
            Rvalue::Discriminant(sp) => {
                let src = self.place(sp, SRC)?;
                self.read_discriminant(&src)?;
                self.store_result(p, dl.size)
            }
            Rvalue::Aggregate(kind, ops) => self.aggregate(p, kind, ops, &dl),
            Rvalue::Repeat(op, n) => {
                let n = self.cx.eval_const(n.subst(self.inst.args))? as u64;
                let elem_ty = self.operand_ty(op);
                let el = self.layout(elem_ty)?;
                let stride = el.size.next_multiple_of(el.align);
                // Evaluate once into a temporary, then copy it into each element.
                let tmp = self.alloc(el.size, el.align);
                self.store_operand(mem(Reg::Rbp, tmp), op, el.size)?;
                for i in 0..n {
                    let d = self.place(p, DEST)?;
                    self.copy_mem(d.mem((i * stride) as i32), mem(Reg::Rbp, tmp), el.size);
                }
                Ok(())
            }
            Rvalue::SizeOf(t) | Rvalue::AlignOf(t) => {
                let l = self.layout(self.mono(*t))?;
                let v = if matches!(rv, Rvalue::SizeOf(_)) {
                    l.size
                } else {
                    l.align
                };
                self.a.mov_ri(Reg::Rax, v);
                self.store_result(p, dl.size)
            }
            Rvalue::OffsetOf(container, steps) => {
                let mut l = self.layout(self.mono(*container))?;
                let mut off = 0u64;
                for &(v, f, t) in steps {
                    let vl = match &l.variants {
                        hyprc_mir::layout::Variants::Multiple { variants, .. } => {
                            variants[v as usize].clone()
                        }
                        _ => l.clone(),
                    };
                    off += vl.field_offset(f as usize);
                    l = self.layout(self.mono(t))?;
                }
                self.a.mov_ri(Reg::Rax, off);
                self.store_result(p, dl.size)
            }
            Rvalue::CopyForDeref(sp) => {
                let src = self.place(sp, SRC)?;
                let d = self.place(p, DEST)?;
                self.copy_mem(d.mem(0), src.mem(0), dl.size);
                Ok(())
            }
            Rvalue::ThreadLocalRef(_) => Err("thread-local statics aren't supported yet".into()),
        }
    }

    fn binary(
        &mut self,
        p: &Place,
        op: BinOp,
        a: &Operand,
        b: &Operand,
        dsize: u64,
        checked: bool,
    ) -> Result<(), String> {
        let ty = self.operand_ty(a);
        if ty.is_float() {
            let double = self.load_float(a, Xmm(0))?;
            self.load_float(b, Xmm(1))?;
            let code = match op {
                BinOp::Add => Some(0x58),
                BinOp::Mul => Some(0x59),
                BinOp::Sub => Some(0x5C),
                BinOp::Div => Some(0x5E),
                _ => None,
            };
            if let Some(code) = code {
                self.a.fp_op(code, double, Xmm(0), Xmm(1));
                let d = self.place(p, DEST)?;
                self.a.store_f(double, d.mem(0), Xmm(0));
                return Ok(());
            }
            // Comparisons: `ucomisd`; NaN compares false (parity flag set).
            let (x, y, cond) = match op {
                BinOp::Eq => (0, 1, Cond::E),
                BinOp::Ne => (0, 1, Cond::Ne),
                BinOp::Lt => (1, 0, Cond::A),
                BinOp::Le => (1, 0, Cond::Ae),
                BinOp::Gt => (0, 1, Cond::A),
                BinOp::Ge => (0, 1, Cond::Ae),
                _ => return Err(format!("float operation {op:?}")),
            };
            self.a.ucomi(double, Xmm(x), Xmm(y));
            self.a.setcc(cond, Reg::Rax);
            self.a
                .setcc(if op == BinOp::Ne { Cond::P } else { Cond::Np }, Reg::Rcx);
            if op == BinOp::Ne {
                self.a.alu_rr(Alu::Or, Size::B8, Reg::Rax, Reg::Rcx);
            } else {
                self.a.alu_rr(Alu::And, Size::B8, Reg::Rax, Reg::Rcx);
            }
            self.a.zx_rr(Size::B8, Reg::Rax, Reg::Rax);
            return self.store_result(p, 1);
        }
        let size = self.layout(ty)?.size;
        if size > 8 {
            return Err(format!(
                "128-bit integer operations aren't supported yet (`{ty}`)"
            ));
        }
        let signed = ty.is_signed();
        self.load_scalar(a, Reg::Rax)?;
        self.a.push(Reg::Rax);
        self.load_scalar(b, Reg::Rcx)?;
        self.a.pop(Reg::Rax);
        let width = Size::from_bytes(size);
        let op_size = if size == 8 { Size::B64 } else { Size::B32 };
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul if checked => {
                let alu = match op {
                    BinOp::Add => Some(Alu::Add),
                    BinOp::Sub => Some(Alu::Sub),
                    _ => None,
                };
                if size >= 4 {
                    let s = if size == 8 { Size::B64 } else { Size::B32 };
                    match alu {
                        Some(alu) => self.a.alu_rr(alu, s, Reg::Rax, Reg::Rcx),
                        None if signed => self.a.imul_rr(s, Reg::Rax, Reg::Rcx),
                        None => self.a.mul(s, Reg::Rcx),
                    }
                    let cond = if signed || alu.is_none() {
                        Cond::O
                    } else {
                        Cond::B
                    };
                    self.a.setcc(cond, Reg::Rdx);
                } else {
                    // 8- and 16-bit: compute wide, check the result fits.
                    match alu {
                        Some(alu) => self.a.alu_rr(alu, Size::B64, Reg::Rax, Reg::Rcx),
                        None => self.a.imul_rr(Size::B64, Reg::Rax, Reg::Rcx),
                    }
                    if signed {
                        self.a.sx_rr(width, Reg::Rcx, Reg::Rax);
                    } else {
                        self.a.zx_rr(width, Reg::Rcx, Reg::Rax);
                    }
                    self.a.alu_rr(Alu::Cmp, Size::B64, Reg::Rcx, Reg::Rax);
                    self.a.setcc(Cond::Ne, Reg::Rdx);
                }
                let d = self.place(p, DEST)?;
                self.store_sized(d.mem(0), Reg::Rax, size);
                let flag_off = d.layout.field_offset(1) as i32;
                self.a.store(Size::B8, d.mem(flag_off), Reg::Rdx);
                let _ = dsize;
                return Ok(());
            }
            BinOp::Add => self.a.alu_rr(Alu::Add, Size::B64, Reg::Rax, Reg::Rcx),
            BinOp::Sub => self.a.alu_rr(Alu::Sub, Size::B64, Reg::Rax, Reg::Rcx),
            BinOp::Mul => self.a.imul_rr(Size::B64, Reg::Rax, Reg::Rcx),
            BinOp::BitAnd => self.a.alu_rr(Alu::And, Size::B64, Reg::Rax, Reg::Rcx),
            BinOp::BitOr => self.a.alu_rr(Alu::Or, Size::B64, Reg::Rax, Reg::Rcx),
            BinOp::BitXor => self.a.alu_rr(Alu::Xor, Size::B64, Reg::Rax, Reg::Rcx),
            BinOp::Div | BinOp::Rem => {
                if signed {
                    self.a.sign_extend_ax(op_size);
                    self.a.idiv(op_size, Reg::Rcx);
                } else {
                    self.a.alu_rr(Alu::Xor, Size::B32, Reg::Rdx, Reg::Rdx);
                    self.a.div(op_size, Reg::Rcx);
                }
                if op == BinOp::Rem {
                    self.a.mov_rr(Size::B64, Reg::Rax, Reg::Rdx);
                }
            }
            BinOp::Shl | BinOp::Shr => {
                let bits = (size * 8) as i32;
                if checked {
                    self.a.alu_ri(Alu::Cmp, Size::B64, Reg::Rcx, bits);
                    self.a.setcc(Cond::Ae, Reg::Rdx);
                }
                self.a.alu_ri(Alu::And, Size::B32, Reg::Rcx, bits - 1);
                let sh = match (op, signed) {
                    (BinOp::Shl, _) => Shift::Shl,
                    (_, true) => Shift::Sar,
                    _ => Shift::Shr,
                };
                self.a.shift_cl(sh, Size::B64, Reg::Rax);
                if checked {
                    let d = self.place(p, DEST)?;
                    self.store_sized(d.mem(0), Reg::Rax, size);
                    let flag_off = d.layout.field_offset(1) as i32;
                    self.a.store(Size::B8, d.mem(flag_off), Reg::Rdx);
                    return Ok(());
                }
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.a.alu_rr(Alu::Cmp, Size::B64, Reg::Rax, Reg::Rcx);
                let cond = match (op, signed) {
                    (BinOp::Eq, _) => Cond::E,
                    (BinOp::Ne, _) => Cond::Ne,
                    (BinOp::Lt, true) => Cond::L,
                    (BinOp::Le, true) => Cond::Le,
                    (BinOp::Gt, true) => Cond::G,
                    (BinOp::Ge, true) => Cond::Ge,
                    (BinOp::Lt, false) => Cond::B,
                    (BinOp::Le, false) => Cond::Be,
                    (BinOp::Gt, false) => Cond::A,
                    _ => Cond::Ae,
                };
                self.a.setcc(cond, Reg::Rax);
                self.a.zx_rr(Size::B8, Reg::Rax, Reg::Rax);
                return self.store_result(p, 1);
            }
            BinOp::Offset => {
                let pointee = match *ty.kind() {
                    TyKind::RawPtr(t, _) | TyKind::Ref(t, _) => t,
                    _ => Ty::U8,
                };
                let l = self.layout(pointee)?;
                let stride = l.size.next_multiple_of(l.align) as i32;
                if stride != 1 {
                    self.a.push(Reg::Rax);
                    self.mul_imm(Reg::Rcx, stride);
                    self.a.pop(Reg::Rax);
                }
                self.a.alu_rr(Alu::Add, Size::B64, Reg::Rax, Reg::Rcx);
            }
            BinOp::Cmp => {
                // -1, 0, 1 as `i8`.
                self.a.alu_rr(Alu::Cmp, Size::B64, Reg::Rax, Reg::Rcx);
                self.a
                    .setcc(if signed { Cond::G } else { Cond::A }, Reg::Rax);
                self.a
                    .setcc(if signed { Cond::L } else { Cond::B }, Reg::Rcx);
                self.a.alu_rr(Alu::Sub, Size::B8, Reg::Rax, Reg::Rcx);
                return self.store_result(p, 1);
            }
        }
        self.store_result(p, size)
    }

    fn unary(&mut self, p: &Place, op: UnOp, a: &Operand, ty: Ty) -> Result<(), String> {
        if ty.is_float() {
            let double = self.load_float(a, Xmm(0))?;
            if op == UnOp::Neg {
                // Flip the sign bit.
                self.a.movq_from_xmm(double, Reg::Rax, Xmm(0));
                self.a
                    .mov_ri(Reg::Rcx, if double { 1u64 << 63 } else { 1u64 << 31 });
                self.a.alu_rr(Alu::Xor, Size::B64, Reg::Rax, Reg::Rcx);
                return self.store_result(p, if double { 8 } else { 4 });
            }
            return Err("`!` on a float".into());
        }
        if op == UnOp::PtrMetadata {
            let (Operand::Copy(sp) | Operand::Move(sp)) = a else {
                return Err("metadata of a constant".into());
            };
            let src = self.place(sp, SRC)?;
            self.a.load(Size::B64, Reg::Rax, src.mem(8));
            return self.store_result(p, 8);
        }
        let size = self.layout(ty)?.size;
        self.load_scalar(a, Reg::Rax)?;
        match op {
            UnOp::Neg => self.a.neg(Size::B64, Reg::Rax),
            UnOp::Not if ty == Ty::BOOL => self.a.alu_ri(Alu::Xor, Size::B64, Reg::Rax, 1),
            UnOp::Not => self.a.not(Size::B64, Reg::Rax),
            UnOp::PtrMetadata => unreachable!(),
        }
        self.store_result(p, size)
    }

    fn cast(&mut self, p: &Place, kind: CastKind, a: &Operand, to: Ty) -> Result<(), String> {
        let from = self.operand_ty(a);
        let tl = self.layout(to)?;
        match kind {
            CastKind::IntToInt | CastKind::PtrToAddr | CastKind::AddrToPtr => {
                let fl = self.layout(from)?;
                if fl.size > 8 || tl.size > 8 {
                    return Err("128-bit integer casts aren't supported yet".into());
                }
                // Enums cast to integers through their discriminant.
                if let TyKind::Adt(..) = *from.kind() {
                    let (Operand::Copy(sp) | Operand::Move(sp)) = a else {
                        return Err("cast of a constant enum".into());
                    };
                    let src = self.place(sp, SRC)?;
                    self.read_discriminant(&src)?;
                    return self.store_result(p, tl.size);
                }
                self.load_scalar(a, Reg::Rax)?;
                self.store_result(p, tl.size)
            }
            CastKind::IntToFloat => {
                self.load_scalar(a, Reg::Rax)?;
                let double = tl.size == 8;
                self.a.cvt_int_to_f(double, true, Xmm(0), Reg::Rax);
                let d = self.place(p, DEST)?;
                self.a.store_f(double, d.mem(0), Xmm(0));
                Ok(())
            }
            CastKind::FloatToInt => {
                let double = self.load_float(a, Xmm(0))?;
                self.a.cvt_f_to_int(double, true, Reg::Rax, Xmm(0));
                self.store_result(p, tl.size)
            }
            CastKind::FloatToFloat => {
                let double = self.load_float(a, Xmm(0))?;
                self.a.cvt_f_f(!double, Xmm(0), Xmm(0));
                let d = self.place(p, DEST)?;
                self.a.store_f(!double, d.mem(0), Xmm(0));
                Ok(())
            }
            CastKind::PtrToPtr | CastKind::Transmute => {
                // Wide to thin keeps the data pointer; same size copies.
                let fl = self.layout(from)?;
                let n = tl.size.min(fl.size);
                let tmp = self.alloc(fl.size, fl.align.max(1));
                self.store_operand(mem(Reg::Rbp, tmp), a, fl.size)?;
                let d = self.place(p, DEST)?;
                self.copy_mem(d.mem(0), mem(Reg::Rbp, tmp), n);
                Ok(())
            }
            CastKind::ReifyFnPointer => {
                let TyKind::FnDef(def, args) = *from.kind() else {
                    return Err(format!("reify `{from}`"));
                };
                let inst = self
                    .cx
                    .resolve(def, args)
                    .ok_or_else(|| format!("can't resolve `{}`", self.cx.tcx.def_path(def)))?;
                let sym = self.cx.symbol_for(inst);
                self.a.lea_rip(Reg::Rax, &sym, 0);
                self.store_result(p, 8)
            }
            CastKind::ClosureFnPointer => {
                Err("closures as function pointers aren't supported yet".into())
            }
            CastKind::Unsize => self.unsize(p, a, from, to),
        }
    }

    fn unsize(&mut self, p: &Place, a: &Operand, from: Ty, to: Ty) -> Result<(), String> {
        let (src_pointee, dst_pointee) = match (*from.kind(), *to.kind()) {
            (
                TyKind::Ref(f, _) | TyKind::RawPtr(f, _),
                TyKind::Ref(t, _) | TyKind::RawPtr(t, _),
            ) => (f, t),
            _ => return Err(format!("unsizing `{from}` to `{to}` isn't supported yet")),
        };
        self.load_scalar(a, Reg::Rax)?;
        let meta = match (*src_pointee.kind(), *dst_pointee.kind()) {
            (TyKind::Array(_, n), TyKind::Slice(_)) => self.cx.eval_const(n)? as u64,
            _ => {
                return Err(format!(
                    "unsizing to `{dst_pointee}` isn't supported yet (trait objects)"
                ));
            }
        };
        let d = self.place(p, DEST)?;
        self.a.store(Size::B64, d.mem(0), Reg::Rax);
        self.a.mov_ri(Reg::Rax, meta);
        self.a.store(Size::B64, d.mem(8), Reg::Rax);
        Ok(())
    }

    // ---------------------------------------------------------------------------------------
    // Enums

    /// Reads an enum's discriminant into rax.
    fn read_discriminant(&mut self, src: &PlaceRef) -> Result<(), String> {
        let ty = src.ty;
        let TyKind::Adt(d, _) = *ty.kind() else {
            self.a.mov_ri(Reg::Rax, 0);
            return Ok(());
        };
        let adt = self.cx.tcx.adt_def(d);
        let discrs = hyprc_mir::discriminants(self.cx.tcx, &adt);
        match &src.layout.variants {
            Variants::Single { index } => {
                let v = discrs.get(*index as usize).copied().unwrap_or(0);
                self.a.mov_ri(Reg::Rax, v as u64);
            }
            Variants::Multiple {
                tag,
                encoding,
                tag_offset,
                ..
            } => {
                let size = tag.prim.size(8);
                let signed = matches!(tag.prim, hyprc_mir::layout::Primitive::Int(_, true));
                self.load_ext(Reg::Rax, src.mem(*tag_offset as i32), size, signed);
                match encoding {
                    TagEncoding::Direct => {}
                    TagEncoding::Niche {
                        untagged,
                        variants_start,
                        variants_end,
                        niche_start,
                    } => {
                        // `tag - niche_start` in range: a niche variant; otherwise the
                        // untagged one.
                        let mask = if size >= 8 {
                            u64::MAX
                        } else {
                            (1u64 << (size * 8)) - 1
                        };
                        self.a.mov_ri(Reg::Rcx, *niche_start as u64);
                        self.a.alu_rr(Alu::Sub, Size::B64, Reg::Rax, Reg::Rcx);
                        if mask != u64::MAX {
                            self.a.mov_ri(Reg::Rcx, mask);
                            self.a.alu_rr(Alu::And, Size::B64, Reg::Rax, Reg::Rcx);
                        }
                        let range = (variants_end - variants_start) as u64;
                        self.a.mov_ri(Reg::Rcx, range);
                        self.a.alu_rr(Alu::Cmp, Size::B64, Reg::Rax, Reg::Rcx);
                        // In range: rax + variants_start; else: untagged.
                        self.a.mov_ri(Reg::Rdx, *variants_start as u64);
                        self.a.alu_rr(Alu::Add, Size::B64, Reg::Rax, Reg::Rdx);
                        self.a.mov_ri(
                            Reg::Rdx,
                            discrs.get(*untagged as usize).copied().unwrap_or(0) as u64,
                        );
                        self.a.cmov(Cond::A, Reg::Rax, Reg::Rdx);
                    }
                }
            }
        }
        Ok(())
    }

    /// Writes the tag for variant `v` of the enum at `d`.
    fn write_tag(&mut self, d: &PlaceRef, v: u32) -> Result<(), String> {
        let TyKind::Adt(def, _) = *d.ty.kind() else {
            return Ok(());
        };
        let full = self.layout(d.ty)?;
        let Variants::Multiple {
            tag,
            encoding,
            tag_offset,
            ..
        } = &full.variants
        else {
            return Ok(());
        };
        let size = tag.prim.size(8);
        let value = match encoding {
            TagEncoding::Direct => {
                let adt = self.cx.tcx.adt_def(def);
                let discrs = hyprc_mir::discriminants(self.cx.tcx, &adt);
                discrs.get(v as usize).copied().unwrap_or(0) as u128
            }
            TagEncoding::Niche {
                untagged,
                variants_start,
                niche_start,
                ..
            } => {
                if v == *untagged {
                    return Ok(());
                }
                niche_start.wrapping_add((v - variants_start) as u128)
            }
        };
        let mask = if size >= 16 {
            u128::MAX
        } else {
            (1u128 << (size * 8)) - 1
        };
        self.store_imm(d.mem(*tag_offset as i32), value & mask, size);
        Ok(())
    }

    fn aggregate(
        &mut self,
        p: &Place,
        kind: &AggregateKind,
        ops: &[Operand],
        dl: &Arc<Layout>,
    ) -> Result<(), String> {
        match kind {
            AggregateKind::Adt(def, v, _, active) => {
                let adt = self.cx.tcx.adt_def(*def);
                let vl = self.cx.lcx.variant_layout(dl, *v);
                for (i, op) in ops.iter().enumerate() {
                    let field = active.map_or(i, |f| f as usize);
                    let off = if adt.is_union() {
                        0
                    } else {
                        vl.field_offset(field) as i32
                    };
                    let ft = self.operand_ty(op);
                    let size = self.layout(ft)?.size;
                    let tmp = self.alloc(size, 8);
                    self.store_operand(mem(Reg::Rbp, tmp), op, size)?;
                    let d = self.place(p, DEST)?;
                    self.copy_mem(d.mem(off), mem(Reg::Rbp, tmp), size);
                }
                if adt.is_enum() {
                    let d = self.place(p, DEST)?;
                    self.write_tag(&d, *v)?;
                }
                Ok(())
            }
            AggregateKind::Array(elem) => {
                let el = self.layout(self.mono(*elem))?;
                let stride = el.size.next_multiple_of(el.align) as i32;
                for (i, op) in ops.iter().enumerate() {
                    let tmp = self.alloc(el.size, el.align);
                    self.store_operand(mem(Reg::Rbp, tmp), op, el.size)?;
                    let d = self.place(p, DEST)?;
                    self.copy_mem(d.mem(i as i32 * stride), mem(Reg::Rbp, tmp), el.size);
                }
                Ok(())
            }
            AggregateKind::Tuple | AggregateKind::Closure(..) | AggregateKind::RawPtr(..) => {
                for (i, op) in ops.iter().enumerate() {
                    let off = dl.field_offset(i) as i32;
                    let ft = self.operand_ty(op);
                    let size = self.layout(ft)?.size;
                    let tmp = self.alloc(size, 8);
                    self.store_operand(mem(Reg::Rbp, tmp), op, size)?;
                    let d = self.place(p, DEST)?;
                    self.copy_mem(d.mem(off), mem(Reg::Rbp, tmp), size);
                }
                Ok(())
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    // Terminators

    fn terminator(&mut self, t: &Terminator) -> Result<(), String> {
        match &t.kind {
            TerminatorKind::Goto(b) => {
                let l = self.labels[b.index()];
                self.a.jmp(l);
            }
            TerminatorKind::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                let ty = self.load_scalar(discr, Reg::Rax)?;
                let size = self.layout(ty)?.size;
                for (v, b) in targets {
                    let v = if ty.is_signed() {
                        hyprc_ty::consteval::sext(*v, ty, self.cx.tcx.pointer_width) as i64
                    } else {
                        *v as i64
                    };
                    if v >= i32::MIN as i64 && v <= i32::MAX as i64 {
                        self.a.alu_ri(Alu::Cmp, Size::B64, Reg::Rax, v as i32);
                    } else {
                        self.a.mov_ri(Reg::Rcx, v as u64);
                        self.a.alu_rr(Alu::Cmp, Size::B64, Reg::Rax, Reg::Rcx);
                    }
                    let l = self.labels[b.index()];
                    self.a.jcc(Cond::E, l);
                }
                let _ = size;
                let l = self.labels[otherwise.index()];
                self.a.jmp(l);
            }
            TerminatorKind::Return => self.ret()?,
            TerminatorKind::Unreachable => self.a.ud2(),
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
            } => {
                self.call(func, args, destination)?;
                match target {
                    Some(b) => {
                        let l = self.labels[b.index()];
                        self.a.jmp(l);
                    }
                    None => self.a.ud2(),
                }
            }
            TerminatorKind::Drop { place, target } => {
                let ty = self.mono(hyprc_mir::mono::place_ty(self.cx.tcx, &self.body, place));
                if self.cx.needs_drop(ty) {
                    return Err(format!("dropping `{ty}` isn't supported yet"));
                }
                let l = self.labels[target.index()];
                self.a.jmp(l);
            }
            TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
            } => {
                self.load_scalar(cond, Reg::Rax)?;
                self.a.test_rr(Size::B8, Reg::Rax, Reg::Rax);
                let l = self.labels[target.index()];
                self.a.jcc(if *expected { Cond::Ne } else { Cond::E }, l);
                self.panic_for(msg)?;
            }
            TerminatorKind::InlineAsm { .. } => {
                return Err("inline assembly isn't supported yet".into());
            }
        }
        Ok(())
    }

    /// A failed assertion: the core panic function for it if there is one, else a trap.
    fn panic_for(&mut self, msg: &AssertKind) -> Result<(), String> {
        let name = match msg {
            AssertKind::BoundsCheck { .. } => "panic_bounds_check",
            AssertKind::Overflow(BinOp::Add) => "panic_const_add_overflow",
            AssertKind::Overflow(BinOp::Sub) => "panic_const_sub_overflow",
            AssertKind::Overflow(BinOp::Mul) => "panic_const_mul_overflow",
            AssertKind::Overflow(BinOp::Div) => "panic_const_div_overflow",
            AssertKind::Overflow(BinOp::Rem) => "panic_const_rem_overflow",
            AssertKind::Overflow(BinOp::Shl) => "panic_const_shl_overflow",
            AssertKind::Overflow(BinOp::Shr) => "panic_const_shr_overflow",
            AssertKind::OverflowNeg => "panic_const_neg_overflow",
            AssertKind::DivisionByZero => "panic_const_div_by_zero",
            AssertKind::RemainderByZero => "panic_const_rem_by_zero",
            _ => "",
        };
        let Some(def) = self.cx.tcx.lang_item(name).filter(|&d| {
            self.cx.tcx.hir.def_kind(d) == DefKind::Fn && self.cx.tcx.generics_of(d).count() == 0
        }) else {
            self.a.ud2();
            return Ok(());
        };
        // The panic function, with the index and length for bounds checks. (`#[track_caller]`
        // locations aren't passed: hyprc doesn't implement them on either side yet.)
        let inst = Instance::item(def, hyprc_ty::Args::EMPTY);
        let sym = self.cx.symbol_for(inst);
        self.cx.request(inst);
        if let AssertKind::BoundsCheck { len, index } = msg {
            self.load_scalar(index, Reg::Rax)?;
            self.a.push(Reg::Rax);
            self.load_scalar(len, Reg::Rsi)?;
            self.a.pop(Reg::Rdi);
        }
        self.a.call_sym(&sym);
        self.a.ud2();
        Ok(())
    }

    fn ret(&mut self) -> Result<(), String> {
        match self.ret_mode.clone() {
            PassMode::Ignore => {}
            PassMode::Direct(classes) => {
                let l = self.layout(self.tys[0])?;
                let Loc::Stack(off) = self.loc[0] else {
                    return Err("return slot".into());
                };
                let mut gpr = [Reg::Rax, Reg::Rdx].into_iter();
                let mut xmm = 0u8;
                for (k, c) in classes.iter().enumerate() {
                    let (o, size) = self.eightbyte(&l, k, classes.len());
                    match c {
                        RegClass::Int => {
                            let r = gpr.next().unwrap();
                            self.load_sized(r, mem(Reg::Rbp, off + o), size);
                        }
                        RegClass::Sse => {
                            self.a.load_f(size == 8, Xmm(xmm), mem(Reg::Rbp, off + o));
                            xmm += 1;
                        }
                    }
                }
            }
            PassMode::Indirect | PassMode::Stack => {
                if let Loc::Indirect(slot) = self.loc[0] {
                    self.a.load(Size::B64, Reg::Rax, mem(Reg::Rbp, slot));
                }
            }
        }
        self.a.mov_rr(Size::B64, Reg::Rsp, Reg::Rbp);
        self.a.pop(Reg::Rbp);
        self.a.ret();
        Ok(())
    }

    fn call(&mut self, func: &Operand, args: &[Operand], dest: &Place) -> Result<(), String> {
        let fty = self.operand_ty(func);
        enum Target {
            Sym(String),
            Ptr,
        }
        let (target, sig_abi, c_variadic) = match *fty.kind() {
            TyKind::FnDef(def, fargs) => {
                let Some(inst) = self.cx.resolve(def, fargs) else {
                    return Err(format!(
                        "can't resolve the call to `{}`",
                        self.cx.tcx.def_path(def)
                    ));
                };
                if let InstanceKind::Intrinsic(d) = inst.kind {
                    return self.intrinsic(d, inst.args, args, dest);
                }
                if matches!(inst.kind, InstanceKind::Virtual(_)) {
                    return Err("calls through `dyn` aren't supported yet".into());
                }
                let sig = self.cx.tcx.fn_sig(def);
                (
                    Target::Sym(self.cx.symbol_for(inst)),
                    sig.abi,
                    sig.c_variadic,
                )
            }
            TyKind::Closure(c, cargs) => {
                let inst = Instance {
                    kind: InstanceKind::Closure(c),
                    args: cargs,
                };
                (Target::Sym(self.cx.symbol_for(inst)), FnAbi::Rust, false)
            }
            TyKind::FnPtr(sig) => (Target::Ptr, sig.abi, sig.c_variadic),
            _ => return Err(format!("call of `{fty}`")),
        };
        let c_abi = matches!(sig_abi, FnAbi::C | FnAbi::System);
        let classify = |l: &Arc<Layout>| {
            if c_abi {
                classify_c(l)
            } else {
                classify_rust(l)
            }
        };
        let dty = self.mono(hyprc_mir::mono::place_ty(self.cx.tcx, &self.body, dest));
        let dl = self.layout(dty)?;
        let mut ret_mode = classify(&dl);
        if ret_mode == PassMode::Stack {
            ret_mode = PassMode::Indirect;
        }
        // 1. Every argument into a frame temporary (the function pointer too).
        let fptr_slot = if matches!(target, Target::Ptr) {
            let s = self.alloc(8, 8);
            self.store_operand(mem(Reg::Rbp, s), func, 8)?;
            Some(s)
        } else {
            None
        };
        let mut temps = Vec::with_capacity(args.len());
        for a in args {
            let t = self.operand_ty(a);
            let l = self.layout(t)?;
            let slot = self.alloc(l.size.max(8), l.align.max(8));
            self.store_operand(mem(Reg::Rbp, slot), a, l.size)?;
            temps.push((slot, l));
        }
        // 2. The return place's address, for indirect returns.
        let ret_ptr_slot = if ret_mode == PassMode::Indirect {
            let d = self.place(dest, DEST)?;
            self.a.lea(Reg::Rax, d.mem(0));
            let s = self.alloc(8, 8);
            self.a.store(Size::B64, mem(Reg::Rbp, s), Reg::Rax);
            Some(s)
        } else {
            None
        };
        // 3. Registers and stack arguments.
        let mut gpr = 0usize;
        let mut xmm = 0u8;
        let mut stack: Vec<(i32, u64)> = Vec::new();
        let mut loads: Vec<(RegClass, u8, i32, u64)> = Vec::new();
        if let Some(s) = ret_ptr_slot {
            loads.push((RegClass::Int, 0, s, 8));
            gpr = 1;
        }
        let mut indirect_ptrs: Vec<(u8, i32)> = Vec::new();
        for (slot, l) in &temps {
            match classify(l) {
                PassMode::Ignore => {}
                PassMode::Direct(classes) => {
                    let ng = classes.iter().filter(|c| **c == RegClass::Int).count();
                    let nx = classes.len() - ng;
                    if gpr + ng > 6 || xmm as usize + nx > 8 {
                        stack.push((*slot, l.size));
                        continue;
                    }
                    for (k, c) in classes.iter().enumerate() {
                        let (o, size) = self.eightbyte(l, k, classes.len());
                        match c {
                            RegClass::Int => {
                                loads.push((RegClass::Int, gpr as u8, slot + o, size));
                                gpr += 1;
                            }
                            RegClass::Sse => {
                                loads.push((RegClass::Sse, xmm, slot + o, size));
                                xmm += 1;
                            }
                        }
                    }
                }
                PassMode::Indirect => {
                    if gpr < 6 {
                        indirect_ptrs.push((gpr as u8, *slot));
                        gpr += 1;
                    } else {
                        stack.push((-(*slot), 0));
                    }
                }
                PassMode::Stack => stack.push((*slot, l.size)),
            }
        }
        // Stack arguments go at [rsp], [rsp + 8], … in order.
        let mut out_off = 0i32;
        for (slot, size) in &stack {
            if *size == 0 {
                // An indirect argument that didn't fit in registers: its address.
                self.a.lea(Reg::Rax, mem(Reg::Rbp, -*slot));
                self.a.store(Size::B64, mem(Reg::Rsp, out_off), Reg::Rax);
                out_off += 8;
            } else {
                self.copy_mem(mem(Reg::Rsp, out_off), mem(Reg::Rbp, *slot), *size);
                out_off += align_up(*size as i32, 8);
            }
        }
        self.max_outgoing = self.max_outgoing.max(out_off as u32);
        for (class, idx, off, size) in loads {
            match class {
                RegClass::Int => self.load_sized(GPR_ARGS[idx as usize], mem(Reg::Rbp, off), size),
                RegClass::Sse => self.a.load_f(size == 8, Xmm(idx), mem(Reg::Rbp, off)),
            }
        }
        for (idx, slot) in indirect_ptrs {
            self.a.lea(GPR_ARGS[idx as usize], mem(Reg::Rbp, slot));
        }
        if c_variadic {
            self.a.mov_ri(Reg::Rax, xmm as u64);
        }
        // 4. The call.
        match target {
            Target::Sym(s) => self.a.call_sym(&s),
            Target::Ptr => {
                self.a
                    .load(Size::B64, Reg::R10, mem(Reg::Rbp, fptr_slot.unwrap()));
                self.a.call_r(Reg::R10);
            }
        }
        // 5. The result.
        if let PassMode::Direct(classes) = ret_mode {
            // Save the return registers while the destination is addressed.
            let tmp = self.alloc(16, 16);
            let mut g = [Reg::Rax, Reg::Rdx].into_iter();
            let mut x = 0u8;
            for (k, c) in classes.iter().enumerate() {
                match c {
                    RegClass::Int => self.a.store(
                        Size::B64,
                        mem(Reg::Rbp, tmp + k as i32 * 8),
                        g.next().unwrap(),
                    ),
                    RegClass::Sse => {
                        self.a
                            .store_f(true, mem(Reg::Rbp, tmp + k as i32 * 8), Xmm(x));
                        x += 1;
                    }
                }
            }
            let d = self.place(dest, DEST)?;
            for k in 0..classes.len() {
                let (o, size) = self.eightbyte(&dl, k, classes.len());
                self.a
                    .load(Size::B64, Reg::Rax, mem(Reg::Rbp, tmp + k as i32 * 8));
                self.store_sized(d.mem(o), Reg::Rax, size);
            }
        }
        Ok(())
    }

    /// Compiler intrinsics, expanded at the call.
    fn intrinsic(
        &mut self,
        def: hyprc_hir::DefId,
        iargs: hyprc_ty::Args,
        args: &[Operand],
        dest: &Place,
    ) -> Result<(), String> {
        let name = self.cx.tcx.hir.name(def);
        match name.as_str() {
            "size_of" | "min_align_of" | "align_of" => {
                let t = iargs.ty(0);
                let l = self.layout(t)?;
                self.a.mov_ri(
                    Reg::Rax,
                    if name.as_str() == "size_of" {
                        l.size
                    } else {
                        l.align
                    },
                );
                self.store_result(dest, 8)
            }
            "abort" | "unreachable" => {
                self.a.ud2();
                Ok(())
            }
            "transmute" | "transmute_unchecked" => {
                let dty = self.mono(hyprc_mir::mono::place_ty(self.cx.tcx, &self.body, dest));
                let size = self.layout(dty)?.size;
                let tmp = self.alloc(size.max(8), 8);
                self.store_operand(mem(Reg::Rbp, tmp), &args[0], size)?;
                let d = self.place(dest, DEST)?;
                self.copy_mem(d.mem(0), mem(Reg::Rbp, tmp), size);
                Ok(())
            }
            "caller_location" => {
                let sym = self.cx.rodata_symbol(&[0u8; 24]);
                self.a.lea_rip(Reg::Rax, &sym, 0);
                self.store_result(dest, 8)
            }
            "ptr_metadata" => {
                let pty = self.operand_ty(&args[0]);
                let l = self.layout(pty)?;
                if l.size > 8 {
                    let tmp = self.alloc(l.size, 8);
                    self.store_operand(mem(Reg::Rbp, tmp), &args[0], l.size)?;
                    self.a.load(Size::B64, Reg::Rax, mem(Reg::Rbp, tmp + 8));
                    self.store_result(dest, 8)?;
                }
                Ok(())
            }
            other => Err(format!("the intrinsic `{other}` isn't supported yet")),
        }
    }
}
