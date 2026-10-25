//! How arguments and return values travel on x86-64.
//!
//! `extern "C"` follows the System V ABI. Rust calls use a simpler convention of hyprc's own
//! (everything hyprc links was compiled by hyprc): scalars and scalar pairs in registers,
//! other aggregates by pointer to a copy, returned through a hidden pointer.

use hyprc_mir::layout::{Abi, FieldsShape, Layout, Primitive};
use std::sync::Arc;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RegClass {
    Int,
    Sse,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PassMode {
    /// Zero-sized or uninhabited: not passed.
    Ignore,
    /// In registers: one class per eightbyte (one or two).
    Direct(Vec<RegClass>),
    /// By pointer to a copy the caller makes.
    Indirect,
    /// On the stack, by value (C `MEMORY` class).
    Stack,
}

/// System V classification of a value for `extern "C"`.
pub fn classify_c(l: &Arc<Layout>) -> PassMode {
    if l.size == 0 {
        return PassMode::Ignore;
    }
    match l.abi {
        Abi::Uninhabited => PassMode::Ignore,
        Abi::Scalar(s) => PassMode::Direct(vec![if s.prim.is_float() {
            RegClass::Sse
        } else {
            RegClass::Int
        }]),
        Abi::ScalarPair(a, b) => {
            // Two eightbytes when each scalar fits one.
            let ca = if a.prim.is_float() {
                RegClass::Sse
            } else {
                RegClass::Int
            };
            let cb = if b.prim.is_float() {
                RegClass::Sse
            } else {
                RegClass::Int
            };
            if l.size <= 8 {
                PassMode::Direct(vec![if ca == RegClass::Sse && cb == RegClass::Sse {
                    RegClass::Sse
                } else {
                    RegClass::Int
                }])
            } else {
                PassMode::Direct(vec![ca, cb])
            }
        }
        Abi::Aggregate { .. } => {
            if l.size > 16 {
                return PassMode::Stack;
            }
            let n = l.size.div_ceil(8) as usize;
            let mut classes = vec![None::<RegClass>; n];
            classify_fields(l, 0, &mut classes);
            PassMode::Direct(
                classes
                    .into_iter()
                    .map(|c| c.unwrap_or(RegClass::Sse))
                    .collect(),
            )
        }
    }
}

fn classify_fields(l: &Layout, offset: u64, out: &mut [Option<RegClass>]) {
    match l.abi {
        Abi::Scalar(s) => mark(out, offset, s.prim),
        Abi::ScalarPair(a, b) => {
            mark(out, offset, a.prim);
            let b_off = offset + l.pair_b_offset(8);
            mark(out, b_off, b.prim);
        }
        _ => {
            // Without field layouts at hand here, be conservative: integer class.
            let n = l.size.div_ceil(8);
            for i in 0..n {
                let idx = ((offset / 8) + i) as usize;
                if idx < out.len() {
                    out[idx] = Some(RegClass::Int);
                }
            }
            let _ = &l.fields;
        }
    }
    if let FieldsShape::Primitive = l.fields {}
}

fn mark(out: &mut [Option<RegClass>], offset: u64, p: Primitive) {
    let idx = (offset / 8) as usize;
    if idx >= out.len() {
        return;
    }
    let c = if p.is_float() {
        RegClass::Sse
    } else {
        RegClass::Int
    };
    out[idx] = Some(match out[idx] {
        Some(RegClass::Int) => RegClass::Int,
        _ => c,
    });
}

/// hyprc's Rust convention.
pub fn classify_rust(l: &Arc<Layout>) -> PassMode {
    if l.size == 0 {
        return PassMode::Ignore;
    }
    match l.abi {
        Abi::Uninhabited => PassMode::Ignore,
        Abi::Scalar(s) if s.prim.size(8) <= 8 => PassMode::Direct(vec![if s.prim.is_float() {
            RegClass::Sse
        } else {
            RegClass::Int
        }]),
        Abi::Scalar(_) => PassMode::Direct(vec![RegClass::Int, RegClass::Int]),
        Abi::ScalarPair(a, b) if a.prim.size(8) <= 8 && b.prim.size(8) <= 8 => {
            PassMode::Direct(vec![
                if a.prim.is_float() {
                    RegClass::Sse
                } else {
                    RegClass::Int
                },
                if b.prim.is_float() {
                    RegClass::Sse
                } else {
                    RegClass::Int
                },
            ])
        }
        _ => PassMode::Indirect,
    }
}
