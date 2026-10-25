//! An x86-64 instruction encoder: the instructions code generation uses, labels with
//! fixups for jumps, and relocations for symbols.

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
#[repr(u8)]
pub enum Reg {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    Rbx = 3,
    Rsp = 4,
    Rbp = 5,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}

impl Reg {
    fn low(self) -> u8 {
        self as u8 & 7
    }

    fn ext(self) -> bool {
        self as u8 >= 8
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Xmm(pub u8);

impl Xmm {
    fn low(self) -> u8 {
        self.0 & 7
    }

    fn ext(self) -> bool {
        self.0 >= 8
    }
}

/// `[base + disp]`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Mem {
    pub base: Reg,
    pub disp: i32,
}

pub fn mem(base: Reg, disp: i32) -> Mem {
    Mem { base, disp }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Size {
    B8,
    B16,
    B32,
    B64,
}

impl Size {
    pub fn from_bytes(n: u64) -> Size {
        match n {
            1 => Size::B8,
            2 => Size::B16,
            4 => Size::B32,
            _ => Size::B64,
        }
    }

    pub fn bytes(self) -> u64 {
        match self {
            Size::B8 => 1,
            Size::B16 => 2,
            Size::B32 => 4,
            Size::B64 => 8,
        }
    }
}

/// Condition codes (the low nibble of `jcc`/`setcc`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Cond {
    O = 0,
    No = 1,
    B = 2,
    Ae = 3,
    E = 4,
    Ne = 5,
    Be = 6,
    A = 7,
    S = 8,
    Ns = 9,
    P = 10,
    Np = 11,
    L = 12,
    Ge = 13,
    Le = 14,
    G = 15,
}

/// The ALU group-1 operations (`/digit` in the encoding).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Alu {
    Add = 0,
    Or = 1,
    Adc = 2,
    Sbb = 3,
    And = 4,
    Sub = 5,
    Xor = 6,
    Cmp = 7,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shift {
    Shl = 4,
    Shr = 5,
    Sar = 7,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Label(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RelocKind {
    /// A call: `S + A - P` through the PLT.
    Plt32,
    /// A PC-relative data reference: `S + A - P`.
    Pc32,
    /// An absolute address (in data): `S + A`.
    Abs64,
}

#[derive(Clone, Debug)]
pub struct Reloc {
    pub offset: u64,
    pub symbol: String,
    pub kind: RelocKind,
    pub addend: i64,
}

#[derive(Default)]
pub struct Asm {
    pub code: Vec<u8>,
    labels: Vec<Option<u32>>,
    /// (offset of the rel32 field, label)
    fixups: Vec<(u32, Label)>,
    pub relocs: Vec<Reloc>,
}

impl Asm {
    pub fn new() -> Asm {
        Asm::default()
    }

    pub fn pos(&self) -> u32 {
        self.code.len() as u32
    }

    fn byte(&mut self, b: u8) {
        self.code.push(b);
    }

    fn u32(&mut self, v: u32) {
        self.code.extend_from_slice(&v.to_le_bytes());
    }

    fn i32(&mut self, v: i32) {
        self.code.extend_from_slice(&v.to_le_bytes());
    }

    // ---------------------------------------------------------------------------------------
    // Labels

    pub fn new_label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() as u32 - 1)
    }

    pub fn bind(&mut self, l: Label) {
        self.labels[l.0 as usize] = Some(self.pos());
    }

    /// Patches jumps to their labels; call once at the end.
    pub fn finish(&mut self) {
        for &(at, l) in &self.fixups {
            let target = self.labels[l.0 as usize].expect("jump to an unbound label");
            let rel = target as i64 - (at as i64 + 4);
            self.code[at as usize..at as usize + 4].copy_from_slice(&(rel as i32).to_le_bytes());
        }
        self.fixups.clear();
    }

    // ---------------------------------------------------------------------------------------
    // Encoding helpers

    /// REX prefix if needed: `w` 64-bit operand, `r` extends ModRM.reg, `b` extends
    /// ModRM.rm/base. `force` for byte registers sil/dil/spl/bpl.
    fn rex(&mut self, w: bool, r: bool, b: bool, force: bool) {
        let v = 0x40 | ((w as u8) << 3) | ((r as u8) << 2) | (b as u8);
        if v != 0x40 || force {
            self.byte(v);
        }
    }

    fn modrm_reg(&mut self, reg: u8, rm: u8) {
        self.byte(0xC0 | ((reg & 7) << 3) | (rm & 7));
    }

    /// ModRM (+SIB) + disp32 for `[base + disp]`.
    fn modrm_mem(&mut self, reg: u8, m: Mem) {
        let base = m.base.low();
        if m.disp == 0 && base != 5 {
            self.byte(((reg & 7) << 3) | base);
            if base == 4 {
                self.byte(0x24);
            }
        } else if (-128..128).contains(&m.disp) {
            self.byte(0x40 | ((reg & 7) << 3) | base);
            if base == 4 {
                self.byte(0x24);
            }
            self.byte(m.disp as i8 as u8);
        } else {
            self.byte(0x80 | ((reg & 7) << 3) | base);
            if base == 4 {
                self.byte(0x24);
            }
            self.i32(m.disp);
        }
    }

    fn size_prefix(&mut self, s: Size) {
        if s == Size::B16 {
            self.byte(0x66);
        }
    }

    /// Byte operations on rsp/rbp/rsi/rdi need a REX to mean spl/bpl/sil/dil.
    fn byte_reg_needs_rex(r: Reg) -> bool {
        matches!(r, Reg::Rsp | Reg::Rbp | Reg::Rsi | Reg::Rdi)
    }

    // ---------------------------------------------------------------------------------------
    // Moves

    /// `mov dst, src`
    pub fn mov_rr(&mut self, s: Size, dst: Reg, src: Reg) {
        self.size_prefix(s);
        let force =
            s == Size::B8 && (Self::byte_reg_needs_rex(dst) || Self::byte_reg_needs_rex(src));
        self.rex(s == Size::B64, src.ext(), dst.ext(), force);
        self.byte(if s == Size::B8 { 0x88 } else { 0x89 });
        self.modrm_reg(src as u8, dst as u8);
    }

    /// `mov dst, [m]`
    pub fn load(&mut self, s: Size, dst: Reg, m: Mem) {
        self.size_prefix(s);
        let force = s == Size::B8 && Self::byte_reg_needs_rex(dst);
        self.rex(s == Size::B64, dst.ext(), m.base.ext(), force);
        self.byte(if s == Size::B8 { 0x8A } else { 0x8B });
        self.modrm_mem(dst as u8, m);
    }

    /// `mov [m], src`
    pub fn store(&mut self, s: Size, m: Mem, src: Reg) {
        self.size_prefix(s);
        let force = s == Size::B8 && Self::byte_reg_needs_rex(src);
        self.rex(s == Size::B64, src.ext(), m.base.ext(), force);
        self.byte(if s == Size::B8 { 0x88 } else { 0x89 });
        self.modrm_mem(src as u8, m);
    }

    /// `mov dst, imm` (the shortest encoding for the value).
    pub fn mov_ri(&mut self, dst: Reg, imm: u64) {
        if imm <= u32::MAX as u64 {
            // `mov r32, imm32` zero-extends.
            self.rex(false, false, dst.ext(), false);
            self.byte(0xB8 + dst.low());
            self.u32(imm as u32);
        } else if (imm as i64) >= i32::MIN as i64 && (imm as i64) <= i32::MAX as i64 {
            // `mov r64, simm32`
            self.rex(true, false, dst.ext(), false);
            self.byte(0xC7);
            self.modrm_reg(0, dst as u8);
            self.i32(imm as i32);
        } else {
            self.rex(true, false, dst.ext(), false);
            self.byte(0xB8 + dst.low());
            self.code.extend_from_slice(&imm.to_le_bytes());
        }
    }

    /// `mov [m], imm32` (sign-extended for 64-bit).
    pub fn store_imm(&mut self, s: Size, m: Mem, imm: i32) {
        self.size_prefix(s);
        self.rex(s == Size::B64, false, m.base.ext(), false);
        self.byte(if s == Size::B8 { 0xC6 } else { 0xC7 });
        self.modrm_mem(0, m);
        match s {
            Size::B8 => self.byte(imm as u8),
            Size::B16 => self.code.extend_from_slice(&(imm as u16).to_le_bytes()),
            _ => self.i32(imm),
        }
    }

    /// Zero-extending load of 1 or 2 bytes: `movzx dst, byte/word [m]`.
    pub fn load_zx(&mut self, from: Size, dst: Reg, m: Mem) {
        match from {
            Size::B8 | Size::B16 => {
                self.rex(true, dst.ext(), m.base.ext(), false);
                self.byte(0x0F);
                self.byte(if from == Size::B8 { 0xB6 } else { 0xB7 });
                self.modrm_mem(dst as u8, m);
            }
            Size::B32 => self.load(Size::B32, dst, m),
            Size::B64 => self.load(Size::B64, dst, m),
        }
    }

    /// Sign-extending load to 64 bits.
    pub fn load_sx(&mut self, from: Size, dst: Reg, m: Mem) {
        match from {
            Size::B8 | Size::B16 => {
                self.rex(true, dst.ext(), m.base.ext(), false);
                self.byte(0x0F);
                self.byte(if from == Size::B8 { 0xBE } else { 0xBF });
                self.modrm_mem(dst as u8, m);
            }
            Size::B32 => {
                self.rex(true, dst.ext(), m.base.ext(), false);
                self.byte(0x63);
                self.modrm_mem(dst as u8, m);
            }
            Size::B64 => self.load(Size::B64, dst, m),
        }
    }

    /// Zero-extend the low `from` bits of a register in place.
    pub fn zx_rr(&mut self, from: Size, dst: Reg, src: Reg) {
        match from {
            Size::B8 | Size::B16 => {
                let force = from == Size::B8 && Self::byte_reg_needs_rex(src);
                self.rex(true, dst.ext(), src.ext(), force);
                self.byte(0x0F);
                self.byte(if from == Size::B8 { 0xB6 } else { 0xB7 });
                self.modrm_reg(dst as u8, src as u8);
            }
            // `mov r32, r32` zero-extends the upper half.
            Size::B32 => self.mov_rr(Size::B32, dst, src),
            Size::B64 => {
                if dst != src {
                    self.mov_rr(Size::B64, dst, src)
                }
            }
        }
    }

    /// Sign-extend the low `from` bits of a register to 64.
    pub fn sx_rr(&mut self, from: Size, dst: Reg, src: Reg) {
        match from {
            Size::B8 | Size::B16 => {
                let force = from == Size::B8 && Self::byte_reg_needs_rex(src);
                self.rex(true, dst.ext(), src.ext(), force);
                self.byte(0x0F);
                self.byte(if from == Size::B8 { 0xBE } else { 0xBF });
                self.modrm_reg(dst as u8, src as u8);
            }
            Size::B32 => {
                self.rex(true, dst.ext(), src.ext(), false);
                self.byte(0x63);
                self.modrm_reg(dst as u8, src as u8);
            }
            Size::B64 => {
                if dst != src {
                    self.mov_rr(Size::B64, dst, src)
                }
            }
        }
    }

    /// `lea dst, [m]`
    pub fn lea(&mut self, dst: Reg, m: Mem) {
        self.rex(true, dst.ext(), m.base.ext(), false);
        self.byte(0x8D);
        self.modrm_mem(dst as u8, m);
    }

    /// `lea dst, [rip + symbol + addend]`
    pub fn lea_rip(&mut self, dst: Reg, symbol: &str, addend: i64) {
        self.rex(true, dst.ext(), false, false);
        self.byte(0x8D);
        self.byte(((dst.low()) << 3) | 5);
        let at = self.pos();
        self.i32(0);
        self.relocs.push(Reloc {
            offset: at as u64,
            symbol: symbol.to_string(),
            kind: RelocKind::Pc32,
            addend: addend - 4,
        });
    }

    // ---------------------------------------------------------------------------------------
    // Arithmetic

    pub fn alu_rr(&mut self, op: Alu, s: Size, dst: Reg, src: Reg) {
        self.size_prefix(s);
        let force =
            s == Size::B8 && (Self::byte_reg_needs_rex(dst) || Self::byte_reg_needs_rex(src));
        self.rex(s == Size::B64, src.ext(), dst.ext(), force);
        self.byte(((op as u8) << 3) | if s == Size::B8 { 0 } else { 1 });
        self.modrm_reg(src as u8, dst as u8);
    }

    pub fn alu_ri(&mut self, op: Alu, s: Size, dst: Reg, imm: i32) {
        self.size_prefix(s);
        let force = s == Size::B8 && Self::byte_reg_needs_rex(dst);
        self.rex(s == Size::B64, false, dst.ext(), force);
        if s == Size::B8 {
            self.byte(0x80);
            self.modrm_reg(op as u8, dst as u8);
            self.byte(imm as u8);
        } else if (-128..128).contains(&imm) {
            self.byte(0x83);
            self.modrm_reg(op as u8, dst as u8);
            self.byte(imm as i8 as u8);
        } else {
            self.byte(0x81);
            self.modrm_reg(op as u8, dst as u8);
            if s == Size::B16 {
                self.code.extend_from_slice(&(imm as u16).to_le_bytes());
            } else {
                self.i32(imm);
            }
        }
    }

    pub fn test_rr(&mut self, s: Size, a: Reg, b: Reg) {
        self.size_prefix(s);
        let force = s == Size::B8 && (Self::byte_reg_needs_rex(a) || Self::byte_reg_needs_rex(b));
        self.rex(s == Size::B64, b.ext(), a.ext(), force);
        self.byte(if s == Size::B8 { 0x84 } else { 0x85 });
        self.modrm_reg(b as u8, a as u8);
    }

    /// `imul dst, src` (2-operand, 16/32/64-bit).
    pub fn imul_rr(&mut self, s: Size, dst: Reg, src: Reg) {
        self.size_prefix(s);
        self.rex(s == Size::B64, dst.ext(), src.ext(), false);
        self.byte(0x0F);
        self.byte(0xAF);
        self.modrm_reg(dst as u8, src as u8);
    }

    /// `imul dst, src, imm32` (64-bit)
    pub fn imul_rri(&mut self, dst: Reg, src: Reg, imm: i32) {
        self.rex(true, dst.ext(), src.ext(), false);
        self.byte(0x69);
        self.modrm_reg(dst as u8, src as u8);
        self.i32(imm);
    }

    /// Group 3 (`F7 /n`): `not`=2, `neg`=3, `mul`=4, `imul`=5, `div`=6, `idiv`=7.
    fn group3(&mut self, n: u8, s: Size, r: Reg) {
        self.size_prefix(s);
        let force = s == Size::B8 && Self::byte_reg_needs_rex(r);
        self.rex(s == Size::B64, false, r.ext(), force);
        self.byte(if s == Size::B8 { 0xF6 } else { 0xF7 });
        self.modrm_reg(n, r as u8);
    }

    pub fn not(&mut self, s: Size, r: Reg) {
        self.group3(2, s, r)
    }

    pub fn neg(&mut self, s: Size, r: Reg) {
        self.group3(3, s, r)
    }

    /// `mul r`: rdx:rax = rax * r (unsigned).
    pub fn mul(&mut self, s: Size, r: Reg) {
        self.group3(4, s, r)
    }

    /// `imul r`: rdx:rax = rax * r (signed, one operand).
    pub fn imul1(&mut self, s: Size, r: Reg) {
        self.group3(5, s, r)
    }

    pub fn div(&mut self, s: Size, r: Reg) {
        self.group3(6, s, r)
    }

    pub fn idiv(&mut self, s: Size, r: Reg) {
        self.group3(7, s, r)
    }

    /// Sign-extend rax into rdx (`cwd`/`cdq`/`cqo`) before a signed division.
    pub fn sign_extend_ax(&mut self, s: Size) {
        match s {
            Size::B16 => {
                self.byte(0x66);
                self.byte(0x99);
            }
            Size::B32 => self.byte(0x99),
            Size::B64 => {
                self.byte(0x48);
                self.byte(0x99);
            }
            Size::B8 => {
                // `cbw` then use ax: callers widen 8-bit division to 16 bits instead.
                self.byte(0x66);
                self.byte(0x98);
            }
        }
    }

    /// Shift by `cl`.
    pub fn shift_cl(&mut self, op: Shift, s: Size, r: Reg) {
        self.size_prefix(s);
        let force = s == Size::B8 && Self::byte_reg_needs_rex(r);
        self.rex(s == Size::B64, false, r.ext(), force);
        self.byte(if s == Size::B8 { 0xD2 } else { 0xD3 });
        self.modrm_reg(op as u8, r as u8);
    }

    pub fn shift_ri(&mut self, op: Shift, s: Size, r: Reg, imm: u8) {
        self.size_prefix(s);
        let force = s == Size::B8 && Self::byte_reg_needs_rex(r);
        self.rex(s == Size::B64, false, r.ext(), force);
        self.byte(if s == Size::B8 { 0xC0 } else { 0xC1 });
        self.modrm_reg(op as u8, r as u8);
        self.byte(imm);
    }

    /// `setcc r8`
    pub fn setcc(&mut self, c: Cond, r: Reg) {
        self.rex(false, false, r.ext(), Self::byte_reg_needs_rex(r));
        self.byte(0x0F);
        self.byte(0x90 + c as u8);
        self.modrm_reg(0, r as u8);
    }

    /// `cmovcc dst, src` (64-bit)
    pub fn cmov(&mut self, c: Cond, dst: Reg, src: Reg) {
        self.rex(true, dst.ext(), src.ext(), false);
        self.byte(0x0F);
        self.byte(0x40 + c as u8);
        self.modrm_reg(dst as u8, src as u8);
    }

    // ---------------------------------------------------------------------------------------
    // Control flow

    pub fn jmp(&mut self, l: Label) {
        self.byte(0xE9);
        let at = self.pos();
        self.i32(0);
        self.fixups.push((at, l));
    }

    pub fn jcc(&mut self, c: Cond, l: Label) {
        self.byte(0x0F);
        self.byte(0x80 + c as u8);
        let at = self.pos();
        self.i32(0);
        self.fixups.push((at, l));
    }

    pub fn call_sym(&mut self, symbol: &str) {
        self.byte(0xE8);
        let at = self.pos();
        self.i32(0);
        self.relocs.push(Reloc {
            offset: at as u64,
            symbol: symbol.to_string(),
            kind: RelocKind::Plt32,
            addend: -4,
        });
    }

    pub fn call_r(&mut self, r: Reg) {
        self.rex(false, false, r.ext(), false);
        self.byte(0xFF);
        self.modrm_reg(2, r as u8);
    }

    pub fn ret(&mut self) {
        self.byte(0xC3);
    }

    pub fn push(&mut self, r: Reg) {
        self.rex(false, false, r.ext(), false);
        self.byte(0x50 + r.low());
    }

    pub fn pop(&mut self, r: Reg) {
        self.rex(false, false, r.ext(), false);
        self.byte(0x58 + r.low());
    }

    pub fn ud2(&mut self) {
        self.byte(0x0F);
        self.byte(0x0B);
    }

    /// `rep movsb`: copies rcx bytes from [rsi] to [rdi].
    pub fn rep_movsb(&mut self) {
        self.byte(0xF3);
        self.byte(0xA4);
    }

    /// `rep stosb`: fills rcx bytes at [rdi] with al.
    pub fn rep_stosb(&mut self) {
        self.byte(0xF3);
        self.byte(0xAA);
    }

    // ---------------------------------------------------------------------------------------
    // SSE

    fn sse(
        &mut self,
        prefix: u8,
        op: u8,
        reg: u8,
        reg_ext: bool,
        rm: Option<(u8, bool)>,
        m: Option<Mem>,
        w: bool,
    ) {
        self.byte(prefix);
        let b_ext = match (rm, m) {
            (Some((_, e)), _) => e,
            (_, Some(m)) => m.base.ext(),
            _ => false,
        };
        self.rex(w, reg_ext, b_ext, false);
        self.byte(0x0F);
        self.byte(op);
        match (rm, m) {
            (Some((r, _)), _) => self.modrm_reg(reg, r),
            (_, Some(m)) => self.modrm_mem(reg, m),
            _ => unreachable!(),
        }
    }

    fn fp_prefix(double: bool) -> u8 {
        if double { 0xF2 } else { 0xF3 }
    }

    /// `movss/movsd xmm, [m]`
    pub fn load_f(&mut self, double: bool, x: Xmm, m: Mem) {
        self.sse(
            Self::fp_prefix(double),
            0x10,
            x.low(),
            x.ext(),
            None,
            Some(m),
            false,
        );
    }

    /// `movss/movsd [m], xmm`
    pub fn store_f(&mut self, double: bool, m: Mem, x: Xmm) {
        self.sse(
            Self::fp_prefix(double),
            0x11,
            x.low(),
            x.ext(),
            None,
            Some(m),
            false,
        );
    }

    /// `addsd`=0x58, `mulsd`=0x59, `subsd`=0x5C, `divsd`=0x5E (and `ss`).
    pub fn fp_op(&mut self, op: u8, double: bool, dst: Xmm, src: Xmm) {
        self.sse(
            Self::fp_prefix(double),
            op,
            dst.low(),
            dst.ext(),
            Some((src.low(), src.ext())),
            None,
            false,
        );
    }

    /// `ucomiss/ucomisd a, b`
    pub fn ucomi(&mut self, double: bool, a: Xmm, b: Xmm) {
        if double {
            self.byte(0x66);
        }
        self.rex(false, a.ext(), b.ext(), false);
        self.byte(0x0F);
        self.byte(0x2E);
        self.modrm_reg(a.low(), b.low());
    }

    /// `cvtsi2ss/sd xmm, r32/r64`
    pub fn cvt_int_to_f(&mut self, double: bool, wide: bool, dst: Xmm, src: Reg) {
        self.sse(
            Self::fp_prefix(double),
            0x2A,
            dst.low(),
            dst.ext(),
            Some((src.low(), src.ext())),
            None,
            wide,
        );
    }

    /// `cvttss/sd2si r32/r64, xmm`
    pub fn cvt_f_to_int(&mut self, double: bool, wide: bool, dst: Reg, src: Xmm) {
        self.sse(
            Self::fp_prefix(double),
            0x2C,
            dst.low(),
            dst.ext(),
            Some((src.low(), src.ext())),
            None,
            wide,
        );
    }

    /// `cvtss2sd` (`to_double`) / `cvtsd2ss`
    pub fn cvt_f_f(&mut self, to_double: bool, dst: Xmm, src: Xmm) {
        self.sse(
            if to_double { 0xF3 } else { 0xF2 },
            0x5A,
            dst.low(),
            dst.ext(),
            Some((src.low(), src.ext())),
            None,
            false,
        );
    }

    /// `movq xmm, r64` (or `movd` for 32-bit)
    pub fn movq_to_xmm(&mut self, wide: bool, dst: Xmm, src: Reg) {
        self.sse(
            0x66,
            0x6E,
            dst.low(),
            dst.ext(),
            Some((src.low(), src.ext())),
            None,
            wide,
        );
    }

    /// `movq r64, xmm` (or `movd`)
    pub fn movq_from_xmm(&mut self, wide: bool, dst: Reg, src: Xmm) {
        self.sse(
            0x66,
            0x7E,
            src.low(),
            src.ext(),
            Some((dst.low(), dst.ext())),
            None,
            wide,
        );
    }

    /// `xorps x, x`
    pub fn xorps(&mut self, a: Xmm, b: Xmm) {
        self.rex(false, a.ext(), b.ext(), false);
        self.byte(0x0F);
        self.byte(0x57);
        self.modrm_reg(a.low(), b.low());
    }

    /// `sqrtsd`
    pub fn sqrt(&mut self, double: bool, dst: Xmm, src: Xmm) {
        self.fp_op(0x51, double, dst, src);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn enc(f: impl FnOnce(&mut Asm)) -> Vec<u8> {
        let mut a = Asm::new();
        f(&mut a);
        a.finish();
        a.code
    }

    #[test]
    fn encodings_match_known_bytes() {
        assert_eq!(
            enc(|a| a.mov_rr(Size::B64, Reg::Rax, Reg::Rcx)),
            [0x48, 0x89, 0xC8]
        );
        assert_eq!(
            enc(|a| a.mov_rr(Size::B64, Reg::R8, Reg::Rax)),
            [0x49, 0x89, 0xC0]
        );
        assert_eq!(
            enc(|a| a.load(Size::B64, Reg::Rax, mem(Reg::Rbp, -8))),
            [0x48, 0x8B, 0x45, 0xF8]
        );
        assert_eq!(
            enc(|a| a.store(Size::B32, mem(Reg::Rsp, 16), Reg::Rdx)),
            [0x89, 0x54, 0x24, 0x10]
        );
        assert_eq!(
            enc(|a| a.load(Size::B8, Reg::Rsi, mem(Reg::Rax, 0))),
            [0x40, 0x8A, 0x30]
        );
        assert_eq!(enc(|a| a.mov_ri(Reg::Rax, 42)), [0xB8, 42, 0, 0, 0]);
        assert_eq!(
            enc(|a| a.alu_rr(Alu::Add, Size::B64, Reg::Rax, Reg::Rcx)),
            [0x48, 0x01, 0xC8]
        );
        assert_eq!(
            enc(|a| a.alu_ri(Alu::Sub, Size::B64, Reg::Rsp, 32)),
            [0x48, 0x83, 0xEC, 0x20]
        );
        assert_eq!(
            enc(|a| a.imul_rr(Size::B64, Reg::Rax, Reg::Rcx)),
            [0x48, 0x0F, 0xAF, 0xC1]
        );
        assert_eq!(enc(|a| a.setcc(Cond::L, Reg::Rax)), [0x0F, 0x9C, 0xC0]);
        assert_eq!(enc(|a| a.push(Reg::Rbp)), [0x55]);
        assert_eq!(
            enc(|a| a.lea(Reg::Rax, mem(Reg::Rbp, -16))),
            [0x48, 0x8D, 0x45, 0xF0]
        );
        assert_eq!(
            enc(|a| a.load_zx(Size::B8, Reg::Rax, mem(Reg::Rcx, 0))),
            [0x48, 0x0F, 0xB6, 0x01]
        );
        assert_eq!(
            enc(|a| a.load_f(true, Xmm(0), mem(Reg::Rbp, -8))),
            [0xF2, 0x0F, 0x10, 0x45, 0xF8]
        );
        assert_eq!(
            enc(|a| a.shift_cl(Shift::Sar, Size::B64, Reg::Rax)),
            [0x48, 0xD3, 0xF8]
        );
        let jmp_self = enc(|a| {
            let l = a.new_label();
            a.bind(l);
            a.jmp(l);
        });
        assert_eq!(jmp_self, [0xE9, 0xFB, 0xFF, 0xFF, 0xFF]);
    }
}
