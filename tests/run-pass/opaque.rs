#![feature(no_core, lang_items, auto_traits, rustc_attrs, unboxed_closures, intrinsics, decl_macro)]
#![allow(internal_features, unused)]
#![no_core]
#![no_main]

#[path = "../ui/minicore.rs"]
mod minicore;
use minicore::*;
use minicore::libc::printf;

fn p(v: i64) {
    unsafe { printf("%ld\n\0" as *const str as *const u8, v) };
}
fn adder(k: i64) -> impl Fn(i64) -> i64 { move |x| x + k }
fn counter() -> impl FnMut() -> i64 { let mut n = 0; move || { n += 1; n } }
fn evens(n: i64) -> impl Iterator<Item = i64> { Evens { i: 0, n } }
struct Evens { i: i64, n: i64 }
impl Iterator for Evens {
    type Item = i64;
    fn next(&mut self) -> Option<i64> { if self.i >= self.n { None } else { self.i += 2; Some(self.i - 2) } }
}
fn apply<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 { f(x) }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = adder(5);
    p(a(10));
    p(apply(adder(7), 1));
    let mut c = counter();
    c();
    p(c());
    let mut s = 0;
    for e in evens(9) { s += e; }
    p(s);
    0
}
