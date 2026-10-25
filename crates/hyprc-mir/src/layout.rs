//! Memory layout of types: size, alignment, field offsets, enum tags, and how values are
//! passed (in one register, two, or memory).
//!
//! `repr(Rust)` layout is unspecified, so hyprc keeps fields in declaration order (simple
//! and deterministic). What Rust guarantees is honored: `repr(C)`, `packed`, `align`,
//! `transparent`, and niches where the null-pointer optimization is promised
//! (`Option<&T>`, `Option<Box<T>>`, `Option<NonNull<T>>`, `Option<NonZero*>`, `Option<fn()>`).

use hyprc_hir::{DefId, FloatTy, IntTy, UintTy};
use hyprc_span::FxHashMap;
use hyprc_ty::collect::AdtDef;
use hyprc_ty::{Args, Const, ConstKind, ExistentialPredicate, Ty, TyCtxt, TyKind};
use std::sync::{Arc, RwLock};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Integer {
    I8,
    I16,
    I32,
    I64,
    I128,
}

impl Integer {
    pub fn size(self) -> u64 {
        match self {
            Integer::I8 => 1,
            Integer::I16 => 2,
            Integer::I32 => 4,
            Integer::I64 => 8,
            Integer::I128 => 16,
        }
    }

    pub fn fitting(min: i128, max: i128, signed: bool) -> Integer {
        for i in [Integer::I8, Integer::I16, Integer::I32, Integer::I64] {
            let bits = i.size() * 8;
            let (lo, hi) = if signed {
                (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
            } else {
                (0, (1i128 << bits) - 1)
            };
            if min >= lo && max <= hi {
                return i;
            }
        }
        Integer::I128
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Primitive {
    Int(Integer, bool),
    F16,
    F32,
    F64,
    F128,
    Pointer,
}

impl Primitive {
    pub fn size(self, ptr: u64) -> u64 {
        match self {
            Primitive::Int(i, _) => i.size(),
            Primitive::F16 => 2,
            Primitive::F32 => 4,
            Primitive::F64 => 8,
            Primitive::F128 => 16,
            Primitive::Pointer => ptr,
        }
    }

    pub fn align(self, ptr: u64) -> u64 {
        self.size(ptr).min(16)
    }

    pub fn is_float(self) -> bool {
        matches!(
            self,
            Primitive::F16 | Primitive::F32 | Primitive::F64 | Primitive::F128
        )
    }
}

/// A scalar and the values it may hold (`start..=end`, wrapping): invalid values are
/// niches enums can use.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Scalar {
    pub prim: Primitive,
    pub start: u128,
    pub end: u128,
}

impl Scalar {
    pub fn full(prim: Primitive, ptr: u64) -> Scalar {
        let bits = prim.size(ptr) * 8;
        let end = if bits >= 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        Scalar {
            prim,
            start: 0,
            end,
        }
    }

    fn mask(&self, ptr: u64) -> u128 {
        let bits = self.prim.size(ptr) * 8;
        if bits >= 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        }
    }

    /// How many invalid values this scalar has.
    pub fn niche_count(&self, ptr: u64) -> u128 {
        let mask = self.mask(ptr);
        let valid = self.end.wrapping_sub(self.start) & mask;
        mask - valid
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Abi {
    Uninhabited,
    Scalar(Scalar),
    ScalarPair(Scalar, Scalar),
    Aggregate { sized: bool },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldsShape {
    Primitive,
    Union(usize),
    Array { stride: u64, count: u64 },
    Arbitrary { offsets: Vec<u64> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TagEncoding {
    /// The tag is the discriminant.
    Direct,
    /// Variants other than `untagged` are encoded in invalid values of a field:
    /// variant `v` is `niche_start + (v - variants_start)`.
    Niche {
        untagged: u32,
        variants_start: u32,
        variants_end: u32,
        niche_start: u128,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Variants {
    Single {
        index: u32,
    },
    Multiple {
        tag: Scalar,
        encoding: TagEncoding,
        tag_offset: u64,
        variants: Vec<Arc<Layout>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub size: u64,
    pub align: u64,
    pub abi: Abi,
    pub fields: FieldsShape,
    pub variants: Variants,
    /// The largest niche anywhere in this layout: its offset and scalar.
    pub niche: Option<(u64, Scalar)>,
}

impl Layout {
    pub fn is_zst(&self) -> bool {
        self.size == 0 && matches!(self.abi, Abi::Aggregate { sized: true } | Abi::Uninhabited)
    }

    /// Where a scalar pair's second scalar is. Not always field 1: the pair may come from
    /// a single field (a wrapper struct, a closure capturing one pair) or a niche variant.
    pub fn pair_b_offset(&self, ptr: u64) -> u64 {
        match self.abi {
            Abi::ScalarPair(a, b) => a.prim.size(ptr).next_multiple_of(b.prim.align(ptr)),
            _ => self.field_offset(1),
        }
    }

    pub fn field_offset(&self, i: usize) -> u64 {
        match &self.fields {
            FieldsShape::Primitive | FieldsShape::Union(_) => 0,
            FieldsShape::Array { stride, .. } => stride * i as u64,
            FieldsShape::Arbitrary { offsets } => offsets.get(i).copied().unwrap_or(0),
        }
    }

    fn scalar(s: Scalar, ptr: u64) -> Layout {
        let size = s.prim.size(ptr);
        let niche = (s.niche_count(ptr) > 0).then_some((0, s));
        Layout {
            size,
            align: s.prim.align(ptr),
            abi: Abi::Scalar(s),
            fields: FieldsShape::Primitive,
            variants: Variants::Single { index: 0 },
            niche,
        }
    }

    fn uninhabited() -> Layout {
        Layout {
            size: 0,
            align: 1,
            abi: Abi::Uninhabited,
            fields: FieldsShape::Arbitrary {
                offsets: Vec::new(),
            },
            variants: Variants::Single { index: 0 },
            niche: None,
        }
    }

    pub fn is_unsized(&self) -> bool {
        matches!(self.abi, Abi::Aggregate { sized: false })
    }
}

#[derive(Debug, Clone)]
pub enum LayoutError {
    Unknown(Ty),
    SizeOverflow(Ty),
}

pub struct LayoutCx<'a, 'h> {
    pub tcx: &'a TyCtxt<'h>,
    cache: RwLock<FxHashMap<Ty, Arc<Layout>>>,
    pub ptr: u64,
}

fn align_to(x: u64, a: u64) -> u64 {
    (x + a - 1) / a * a
}

impl<'a, 'h> LayoutCx<'a, 'h> {
    pub fn new(tcx: &'a TyCtxt<'h>) -> Self {
        LayoutCx {
            tcx,
            cache: RwLock::new(FxHashMap::default()),
            ptr: tcx.pointer_width as u64 / 8,
        }
    }

    pub fn layout_of(&self, ty: Ty) -> Result<Arc<Layout>, LayoutError> {
        if let Some(l) = self.cache.read().unwrap().get(&ty) {
            return Ok(l.clone());
        }
        let l = Arc::new(self.compute(ty)?);
        self.cache.write().unwrap().insert(ty, l.clone());
        Ok(l)
    }

    fn int(&self, i: Integer, signed: bool) -> Layout {
        Layout::scalar(Scalar::full(Primitive::Int(i, signed), self.ptr), self.ptr)
    }

    fn ptr_scalar(&self, non_null: bool) -> Scalar {
        let mut s = Scalar::full(Primitive::Pointer, self.ptr);
        if non_null {
            s.start = 1;
        }
        s
    }

    /// The metadata of a pointer to `pointee`: `None` for thin pointers.
    pub fn pointee_metadata(&self, pointee: Ty) -> Option<Scalar> {
        match *pointee.kind() {
            TyKind::Slice(_) | TyKind::Str => Some(Scalar::full(
                Primitive::Int(self.usize_int(), false),
                self.ptr,
            )),
            TyKind::Dynamic(_) => Some(self.ptr_scalar(true)),
            TyKind::Adt(d, args) => {
                // A struct whose last field is unsized has that field's metadata.
                let adt = self.tcx.adt_def(d);
                if adt.is_struct()
                    && let Some(last) = adt.variants.first().and_then(|v| v.fields.last())
                {
                    let t = last.ty.subst(args);
                    if t != pointee {
                        return self.pointee_metadata(t);
                    }
                }
                None
            }
            TyKind::Tuple(ts) => ts.as_slice().last().and_then(|&t| self.pointee_metadata(t)),
            _ => None,
        }
    }

    fn usize_int(&self) -> Integer {
        if self.ptr == 8 {
            Integer::I64
        } else {
            Integer::I32
        }
    }

    fn pointer_layout(&self, pointee: Ty, non_null: bool) -> Layout {
        let data = self.ptr_scalar(non_null);
        match self.pointee_metadata(pointee) {
            None => Layout::scalar(data, self.ptr),
            Some(meta) => {
                let size = self.ptr * 2;
                Layout {
                    size,
                    align: self.ptr,
                    abi: Abi::ScalarPair(data, meta),
                    fields: FieldsShape::Arbitrary {
                        offsets: vec![0, self.ptr],
                    },
                    variants: Variants::Single { index: 0 },
                    niche: non_null.then_some((0, data)),
                }
            }
        }
    }

    fn compute(&self, ty: Ty) -> Result<Layout, LayoutError> {
        let ptr = self.ptr;
        Ok(match *ty.kind() {
            TyKind::Bool => Layout::scalar(
                Scalar {
                    prim: Primitive::Int(Integer::I8, false),
                    start: 0,
                    end: 1,
                },
                ptr,
            ),
            TyKind::Char => Layout::scalar(
                Scalar {
                    prim: Primitive::Int(Integer::I32, false),
                    start: 0,
                    end: 0x10FFFF,
                },
                ptr,
            ),
            TyKind::Int(i) => self.int(int_of(i, self.usize_int()), true),
            TyKind::Uint(u) => self.int(uint_of(u, self.usize_int()), false),
            TyKind::Float(f) => {
                let p = match f {
                    FloatTy::F16 => Primitive::F16,
                    FloatTy::F32 => Primitive::F32,
                    FloatTy::F64 => Primitive::F64,
                    FloatTy::F128 => Primitive::F128,
                };
                Layout::scalar(Scalar::full(p, ptr), ptr)
            }
            TyKind::Never => Layout::uninhabited(),
            // The base type with fewer valid values in its (first) scalar: niches.
            TyKind::Pat(base, r) => {
                let mut l = (*self.layout_of(base)?).clone();
                let restrict = |s: Scalar| Scalar {
                    start: r.start,
                    end: r.end,
                    ..s
                };
                l.abi = match l.abi {
                    Abi::Scalar(s) => Abi::Scalar(restrict(s)),
                    Abi::ScalarPair(a, b) => Abi::ScalarPair(restrict(a), b),
                    other => other,
                };
                if let Abi::Scalar(s) | Abi::ScalarPair(s, _) = l.abi {
                    l.niche = (s.niche_count(ptr) > 0).then_some((0, s));
                }
                l
            }
            TyKind::Ref(inner, _) => self.pointer_layout(inner, true),
            TyKind::RawPtr(inner, _) => self.pointer_layout(inner, false),
            TyKind::FnPtr(_) => Layout::scalar(self.ptr_scalar(true), ptr),
            TyKind::FnDef(..) => self.struct_layout(&[], false, None, None, false)?,
            TyKind::Str => self.unsized_array(Ty::U8)?,
            TyKind::Slice(e) => self.unsized_array(e)?,
            TyKind::Dynamic(_) | TyKind::Foreign(_) => Layout {
                size: 0,
                align: 1,
                abi: Abi::Aggregate { sized: false },
                fields: FieldsShape::Arbitrary {
                    offsets: Vec::new(),
                },
                variants: Variants::Single { index: 0 },
                niche: None,
            },
            TyKind::Array(e, len) => {
                let el = self.layout_of(e)?;
                let n = self.eval_len(len).ok_or(LayoutError::Unknown(ty))?;
                let stride = align_to(el.size, el.align);
                let size = stride.checked_mul(n).ok_or(LayoutError::SizeOverflow(ty))?;
                let abi = if n == 0 {
                    Abi::Aggregate { sized: true }
                } else if matches!(el.abi, Abi::Uninhabited) {
                    Abi::Uninhabited
                } else {
                    Abi::Aggregate { sized: true }
                };
                Layout {
                    size,
                    align: el.align,
                    abi,
                    fields: FieldsShape::Array { stride, count: n },
                    variants: Variants::Single { index: 0 },
                    niche: if n > 0 { el.niche } else { None },
                }
            }
            TyKind::Tuple(ts) => {
                let fields: Vec<Arc<Layout>> = ts
                    .as_slice()
                    .iter()
                    .map(|&t| self.layout_of(t))
                    .collect::<Result<_, _>>()?;
                self.struct_layout(&fields, false, None, None, false)?
            }
            TyKind::Closure(_, args) | TyKind::Coroutine(_, args) => {
                let upvars = hyprc_ty::traits::closure_upvars_from_args(args).unwrap_or_default();
                let fields: Vec<Arc<Layout>> = upvars
                    .iter()
                    .map(|&t| self.layout_of(t))
                    .collect::<Result<_, _>>()?;
                self.struct_layout(&fields, false, None, None, false)?
            }
            TyKind::Adt(d, args) => self.adt_layout(ty, d, args)?,
            TyKind::Param(..) | TyKind::Infer(_) | TyKind::Alias(..) | TyKind::Error => {
                return Err(LayoutError::Unknown(ty));
            }
        })
    }

    fn eval_len(&self, c: Const) -> Option<u64> {
        match c.kind() {
            ConstKind::Value(v) => Some(v as u64),
            ConstKind::Unevaluated { .. } => self.tcx_eval(c),
            _ => None,
        }
    }

    fn tcx_eval(&self, c: Const) -> Option<u64> {
        if let ConstKind::Unevaluated { body, args, .. } = c.kind() {
            let r = self
                .tcx
                .eval_const_body(hyprc_hir::BodyId(body), c.ty(), args);
            return r.try_to_usize();
        }
        None
    }

    fn unsized_array(&self, elem: Ty) -> Result<Layout, LayoutError> {
        let el = self.layout_of(elem)?;
        Ok(Layout {
            size: 0,
            align: el.align,
            abi: Abi::Aggregate { sized: false },
            fields: FieldsShape::Array {
                stride: align_to(el.size, el.align),
                count: 0,
            },
            variants: Variants::Single { index: 0 },
            niche: None,
        })
    }

    /// Fields in order, each at the next offset its alignment allows.
    fn struct_layout(
        &self,
        fields: &[Arc<Layout>],
        c: bool,
        packed: Option<u64>,
        align: Option<u64>,
        transparent: bool,
    ) -> Result<Layout, LayoutError> {
        let _ = c;
        let mut offset = 0u64;
        let mut max_align = 1u64;
        let mut offsets = Vec::with_capacity(fields.len());
        let mut sized = true;
        let mut uninhabited = false;
        let mut niche: Option<(u64, Scalar)> = None;
        for f in fields {
            let a = match packed {
                Some(p) => f.align.min(p),
                None => f.align,
            };
            offset = align_to(offset, a);
            offsets.push(offset);
            if let Some((o, s)) = f.niche
                && niche.is_none_or(|(_, n)| s.niche_count(self.ptr) > n.niche_count(self.ptr))
            {
                niche = Some((offset + o, s));
            }
            offset += f.size;
            max_align = max_align.max(a);
            sized &= !f.is_unsized();
            uninhabited |= matches!(f.abi, Abi::Uninhabited);
        }
        if let Some(a) = align {
            max_align = max_align.max(a);
        }
        let size = align_to(offset, max_align);
        // Newtypes and pairs keep their scalar ABI, so they go in registers.
        let non_zst: Vec<(usize, &Arc<Layout>)> = fields
            .iter()
            .enumerate()
            .filter(|(_, f)| f.size > 0 || matches!(f.abi, Abi::Uninhabited))
            .collect();
        let abi = if uninhabited {
            Abi::Uninhabited
        } else if !sized {
            Abi::Aggregate { sized: false }
        } else if packed.is_some() {
            Abi::Aggregate { sized: true }
        } else if non_zst.len() == 1 && non_zst[0].1.size == size && offsets[non_zst[0].0] == 0 {
            match non_zst[0].1.abi {
                a @ (Abi::Scalar(_) | Abi::ScalarPair(..)) => a,
                _ => Abi::Aggregate { sized: true },
            }
        } else if non_zst.len() == 2 && !transparent {
            match (non_zst[0].1.abi, non_zst[1].1.abi) {
                (Abi::Scalar(a), Abi::Scalar(b)) => {
                    let (o0, o1) = (offsets[non_zst[0].0], offsets[non_zst[1].0]);
                    let b_off = align_to(a.prim.size(self.ptr), b.prim.align(self.ptr));
                    if o0 == 0
                        && o1 == b_off
                        && align_to(b_off + b.prim.size(self.ptr), max_align) == size
                    {
                        Abi::ScalarPair(a, b)
                    } else {
                        Abi::Aggregate { sized: true }
                    }
                }
                _ => Abi::Aggregate { sized: true },
            }
        } else {
            Abi::Aggregate { sized: true }
        };
        Ok(Layout {
            size,
            align: max_align,
            abi,
            fields: FieldsShape::Arbitrary { offsets },
            variants: Variants::Single { index: 0 },
            niche,
        })
    }

    fn adt_layout(&self, ty: Ty, d: DefId, args: Args) -> Result<Layout, LayoutError> {
        let adt = self.tcx.adt_def(d);
        let repr = &adt.repr;
        let field_layouts = |v: usize| -> Result<Vec<Arc<Layout>>, LayoutError> {
            adt.variants[v]
                .fields
                .iter()
                .map(|f| self.layout_of(self.tcx_normalize(f.ty.subst(args))))
                .collect()
        };
        if adt.is_union() {
            let fields = field_layouts(0)?;
            let mut size = 0;
            let mut align = 1;
            for f in &fields {
                size = size.max(f.size);
                align = align.max(f.align);
            }
            if let Some(a) = repr.align {
                align = align.max(a);
            }
            if let Some(p) = repr.packed {
                align = align.min(p);
            }
            return Ok(Layout {
                size: align_to(size, align),
                align,
                abi: Abi::Aggregate { sized: true },
                fields: FieldsShape::Union(fields.len()),
                variants: Variants::Single { index: 0 },
                niche: None,
            });
        }
        if adt.is_struct() {
            let fields = field_layouts(0)?;
            let mut l =
                self.struct_layout(&fields, repr.c, repr.packed, repr.align, repr.transparent)?;
            // `#[rustc_layout_scalar_valid_range_start(1)]` (`NonNull`, `NonZero` internals).
            if let Some(start) = self.valid_range_start(d)
                && let Abi::Scalar(mut s) = l.abi
            {
                s.start = start;
                l.abi = Abi::Scalar(s);
                l.niche = (s.niche_count(self.ptr) > 0).then_some((0, s));
            }
            return Ok(l);
        }
        self.enum_layout(ty, &adt, args)
    }

    fn valid_range_start(&self, d: DefId) -> Option<u128> {
        let item = self.tcx.hir.get_item(d)?;
        item.attrs
            .rustc
            .iter()
            .any(|s| s.as_str() == "rustc_layout_scalar_valid_range_start")
            .then_some(1)
    }

    fn tcx_normalize(&self, t: Ty) -> Ty {
        crate::normalize_erasing(self.tcx, t)
    }

    /// Discriminant values of an enum's variants.
    pub fn discriminants(&self, adt: &AdtDef) -> Vec<i128> {
        let mut out = Vec::with_capacity(adt.variants.len());
        let mut next: i128 = 0;
        let repr_ty = adt
            .repr
            .int
            .map(hyprc_ty::lower_ty::prim_ty)
            .unwrap_or(Ty::ISIZE);
        for v in &adt.variants {
            if let Some(b) = v.discr_body {
                let c = self.tcx.eval_const_body(b, repr_ty, Args::EMPTY);
                if let Some(bits) = c.try_to_bits() {
                    next = if repr_ty.is_signed() {
                        hyprc_ty::consteval::sext(bits, repr_ty, self.tcx.pointer_width)
                    } else {
                        bits as i128
                    };
                }
            }
            out.push(next);
            next = next.wrapping_add(1);
        }
        out
    }

    fn enum_layout(&self, ty: Ty, adt: &AdtDef, args: Args) -> Result<Layout, LayoutError> {
        let n = adt.variants.len();
        if n == 0 {
            return Ok(Layout::uninhabited());
        }
        let variant_fields: Vec<Vec<Arc<Layout>>> = (0..n)
            .map(|v| {
                adt.variants[v]
                    .fields
                    .iter()
                    .map(|f| self.layout_of(self.tcx_normalize(f.ty.subst(args))))
                    .collect::<Result<_, _>>()
            })
            .collect::<Result<_, _>>()?;
        let absent = |v: &Vec<Arc<Layout>>| v.iter().any(|f| matches!(f.abi, Abi::Uninhabited));
        let discrs = self.discriminants(adt);
        let explicit_repr = adt.repr.int.is_some() || adt.repr.c;
        // A single variant without explicit discriminants: a struct.
        if n == 1 && !explicit_repr && adt.variants[0].discr_body.is_none() {
            let mut l = self.struct_layout(&variant_fields[0], false, None, None, false)?;
            l.variants = Variants::Single { index: 0 };
            return Ok(l);
        }
        // Niche filling: one variant with data, the others empty.
        if !explicit_repr {
            let dataful: Vec<usize> = (0..n)
                .filter(|&v| variant_fields[v].iter().any(|f| f.size > 0))
                .collect();
            if dataful.len() == 1 {
                let dv = dataful[0];
                let others_empty = (0..n)
                    .filter(|&v| v != dv)
                    .all(|v| variant_fields[v].iter().all(|f| f.size == 0));
                let st = self.struct_layout(&variant_fields[dv], false, None, None, false)?;
                if others_empty && let Some((niche_off, niche)) = st.niche {
                    let needed = (n - 1) as u128;
                    if niche.niche_count(self.ptr) >= needed {
                        let mask = niche.mask(self.ptr);
                        let niche_start = niche.end.wrapping_add(1) & mask;
                        let variants_start = if dv == 0 { 1 } else { 0 };
                        let variants_end = (n - 1) as u32;
                        let tag = Scalar {
                            prim: niche.prim,
                            start: niche.start,
                            end: niche.end.wrapping_add(needed) & mask,
                        };
                        let variants: Vec<Arc<Layout>> = (0..n)
                            .map(|v| {
                                let mut l = if v == dv {
                                    st.clone()
                                } else {
                                    self.struct_layout(&variant_fields[v], false, None, None, false)
                                        .unwrap()
                                };
                                l.variants = Variants::Single { index: v as u32 };
                                Arc::new(l)
                            })
                            .collect();
                        let abi = match st.abi {
                            Abi::Scalar(_) if niche_off == 0 => Abi::Scalar(tag),
                            Abi::ScalarPair(a, b) => {
                                if niche_off == 0 {
                                    Abi::ScalarPair(tag, b)
                                } else {
                                    Abi::ScalarPair(a, tag)
                                }
                            }
                            _ => Abi::Aggregate { sized: true },
                        };
                        let remaining = Scalar {
                            start: tag.start,
                            end: tag.end,
                            ..niche
                        };
                        return Ok(Layout {
                            size: st.size,
                            align: st.align,
                            abi,
                            fields: FieldsShape::Arbitrary {
                                offsets: vec![niche_off],
                            },
                            variants: Variants::Multiple {
                                tag,
                                encoding: TagEncoding::Niche {
                                    untagged: dv as u32,
                                    variants_start,
                                    variants_end,
                                    niche_start,
                                },
                                tag_offset: niche_off,
                                variants,
                            },
                            niche: (remaining.niche_count(self.ptr) > 0)
                                .then_some((niche_off, remaining)),
                        });
                    }
                }
            }
        }
        // A tag first, then each variant's fields.
        let (min, max) = discrs.iter().fold((i128::MAX, i128::MIN), |(lo, hi), &d| {
            (lo.min(d), hi.max(d))
        });
        let (tag_int, signed) = match adt.repr.int {
            Some(p) => {
                let t = hyprc_ty::lower_ty::prim_ty(p);
                match *t.kind() {
                    TyKind::Int(i) => (int_of(i, self.usize_int()), true),
                    TyKind::Uint(u) => (uint_of(u, self.usize_int()), false),
                    _ => (Integer::I32, true),
                }
            }
            None if adt.repr.c => (Integer::I32, true),
            None => (Integer::fitting(min, max, min < 0), min < 0),
        };
        let tag_size = tag_int.size();
        let mask = if tag_size >= 16 {
            u128::MAX
        } else {
            (1u128 << (tag_size * 8)) - 1
        };
        let tag = Scalar {
            prim: Primitive::Int(tag_int, signed),
            start: (min as u128) & mask,
            end: (max as u128) & mask,
        };
        let tag_layout = Arc::new(Layout::scalar(tag, self.ptr));
        let mut size = tag_size;
        let mut align = tag_size;
        let mut variants = Vec::with_capacity(n);
        for (v, fields) in variant_fields.iter().enumerate() {
            let mut all = vec![tag_layout.clone()];
            all.extend(fields.iter().cloned());
            let mut l = self.struct_layout(&all, true, None, None, false)?;
            // Variant layouts list only the variant's own fields.
            if let FieldsShape::Arbitrary { offsets } = &mut l.fields {
                offsets.remove(0);
            }
            if absent(fields) {
                l.abi = Abi::Uninhabited;
            }
            size = size.max(l.size);
            align = align.max(l.align);
            l.variants = Variants::Single { index: v as u32 };
            variants.push(Arc::new(l));
        }
        if let Some(a) = adt.repr.align {
            align = align.max(a);
        }
        let size = align_to(size, align);
        let all_uninhabited = variant_fields.iter().all(absent);
        let abi = if all_uninhabited {
            Abi::Uninhabited
        } else if variant_fields.iter().all(|f| f.iter().all(|l| l.size == 0)) {
            Abi::Scalar(tag)
        } else {
            Abi::Aggregate { sized: true }
        };
        let _ = ty;
        Ok(Layout {
            size,
            align,
            abi,
            fields: FieldsShape::Arbitrary { offsets: vec![0] },
            variants: Variants::Multiple {
                tag,
                encoding: TagEncoding::Direct,
                tag_offset: 0,
                variants,
            },
            niche: (tag.niche_count(self.ptr) > 0).then_some((0, tag)),
        })
    }

    /// The layout of a variant (for `Downcast`).
    pub fn variant_layout(&self, l: &Arc<Layout>, v: u32) -> Arc<Layout> {
        match &l.variants {
            Variants::Single { .. } => l.clone(),
            Variants::Multiple { variants, .. } => variants[v as usize].clone(),
        }
    }

    /// Is a `dyn` type's principal (for vtables)?
    pub fn dyn_principal(&self, t: Ty) -> Option<DefId> {
        match *t.kind() {
            TyKind::Dynamic(p) => p.as_slice().iter().find_map(|p| match p {
                ExistentialPredicate::Trait { def, .. } => Some(*def),
                _ => None,
            }),
            _ => None,
        }
    }
}

fn int_of(i: IntTy, usize_int: Integer) -> Integer {
    match i {
        IntTy::Isize => usize_int,
        IntTy::I8 => Integer::I8,
        IntTy::I16 => Integer::I16,
        IntTy::I32 => Integer::I32,
        IntTy::I64 => Integer::I64,
        IntTy::I128 => Integer::I128,
    }
}

fn uint_of(u: UintTy, usize_int: Integer) -> Integer {
    match u {
        UintTy::Usize => usize_int,
        UintTy::U8 => Integer::I8,
        UintTy::U16 => Integer::I16,
        UintTy::U32 => Integer::I32,
        UintTy::U64 => Integer::I64,
        UintTy::U128 => Integer::I128,
    }
}
