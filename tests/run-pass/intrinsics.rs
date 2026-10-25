#![feature(no_core, lang_items, auto_traits, rustc_attrs, unboxed_closures, intrinsics, decl_macro)]
#![allow(internal_features, unused)]
#![no_core]
#![no_main]

#[path = "../ui/minicore.rs"]
mod minicore;
use minicore::*;
use minicore::libc::printf;

extern "rust-intrinsic" {
    #[rustc_intrinsic]
    fn black_box<T>(value: T) -> T;

    #[rustc_intrinsic]
    fn likely(value: bool) -> bool;

    #[rustc_intrinsic]
    fn unlikely(value: bool) -> bool;
}

fn p(v: u64) {
    unsafe { printf("%lu\n\0" as *const str as *const u8, v) };
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    p(unsafe { black_box(40) } + 2);
    p(unsafe { likely(true) } as u64 + unsafe { unlikely(false) } as u64);
    0
}
