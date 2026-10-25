#![feature(no_core, lang_items, auto_traits, rustc_attrs, unboxed_closures, intrinsics, decl_macro)]
#![allow(internal_features, unused)]
#![no_core]
#![no_main]

#[path = "../ui/minicore.rs"]
mod minicore;
use minicore::*;
use minicore::libc::printf;

static mut CALLS: u64 = 0;

fn next() -> u64 {
    unsafe {
        CALLS += 1;
        CALLS
    }
}

fn p(v: u64) {
    unsafe { printf("%lu\n\0" as *const str as *const u8, v) };
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let values = [next(); 65536];
    p(unsafe { CALLS });
    p(values[0] + values[65535]);
    0
}
