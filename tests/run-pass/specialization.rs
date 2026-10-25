#![feature(no_core, lang_items, auto_traits, rustc_attrs, unboxed_closures, intrinsics, decl_macro, specialization)]
#![allow(internal_features, unused, incomplete_features)]
#![no_core]
#![no_main]

#[path = "../ui/minicore.rs"]
mod minicore;
use minicore::*;
use minicore::libc::printf;

fn p(v: i64) {
    unsafe { printf("%ld\n\0" as *const str as *const u8, v) };
}
pub trait Marker {}
impl Marker for i64 {}
pub trait Describe { type Out; fn describe(&self) -> i64; fn twice(&self) -> i64 { self.describe() * 2 } }
impl<T> Describe for T { type Out = u8; default fn describe(&self) -> i64 { 1 } }
impl<T: Marker> Describe for T { fn describe(&self) -> i64 { 2 } }
fn out_of<T: Marker>(x: T) -> <T as Describe>::Out { 7 }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    p(5i64.describe());
    p(true.describe());
    p(5i64.twice());
    p(out_of(3i64) as i64);
    0
}
