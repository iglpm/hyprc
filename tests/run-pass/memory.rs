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
static mut COUNTER: i64 = 5;
static LIMIT: i64 = 100;
const SCALE: i64 = 3 * 4;

fn bump(by: i64) -> i64 {
    unsafe {
        COUNTER += by;
        COUNTER
    }
}

fn sum(xs: &[i64], n: usize) -> i64 {
    let mut s = 0;
    let mut i = 0;
    while i < n {
        s += xs[i];
        i += 1;
    }
    s
}

fn fill(xs: &mut [i64; 4], v: i64) {
    let mut i = 0;
    while i < 4 {
        xs[i] = v + i as i64;
        i += 1;
    }
}

fn swap_ptr(a: *mut i64, b: *mut i64) {
    unsafe {
        let t = *a;
        *a = *b;
        *b = t;
    }
}

fn largest<'a>(a: &'a i64, b: &'a i64) -> &'a i64 {
    if *a > *b { a } else { b }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut arr = [0i64; 4];
    fill(&mut arr, 10);
    p(arr[0] + arr[3]);
    p(sum(&arr, 4));
    let mut a = 1;
    let mut b = 2;
    swap_ptr(&mut a, &mut b);
    p(a * 10 + b);
    p(bump(10));
    p(bump(1));
    p(LIMIT + SCALE);
    let r = &mut a;
    *r += 40;
    p(a);
    p(*largest(&a, &b));
    let grid = [[1i64, 2, 3], [4, 5, 6]];
    p(grid[1][2] + grid[0][0]);
    let bytes = b"hey";
    p(bytes[1] as i64);
    let tuple = (1u8, 2u16, 3u32, 4u64);
    p(tuple.0 as i64 + tuple.1 as i64 + tuple.2 as i64 + tuple.3 as i64);
    let mut pt = (5, 6);
    let pr = &mut pt;
    pr.1 = 60;
    p(pt.1 as i64);
    let x = 7;
    let rx = &x;
    let rrx = &rx;
    p(**rrx);
    0
}
