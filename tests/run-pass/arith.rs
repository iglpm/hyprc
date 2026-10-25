//! Integer and float arithmetic, comparisons, casts.
#![feature(no_core, lang_items, auto_traits, rustc_attrs, unboxed_closures, intrinsics, decl_macro)]
#![allow(internal_features, unused)]
#![no_core]
#![no_main]

#[path = "../ui/minicore.rs"]
mod minicore;
use minicore::*;
use minicore::libc::printf;

fn show(name: &str, v: i64) {
    unsafe { printf("%s = %ld\n\0" as *const str as *const u8, name as *const str as *const u8, v) };
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a: i32 = 1000;
    let b: i32 = -7;
    show("a+b\0", (a + b) as i64);
    show("a-b\0", (a - b) as i64);
    show("a*b\0", (a * b) as i64);
    show("a/b\0", (a / b) as i64);
    show("a%b\0", (a % b) as i64);
    show("b/2\0", (b / 2) as i64);
    show("b%2\0", (b % 2) as i64);
    let u: u32 = 4000000000;
    show("u/7\0", (u / 7) as i64);
    show("u%7\0", (u % 7) as i64);
    show("u>>3\0", (u >> 3) as i64);
    show("b>>1\0", (b >> 1) as i64);
    show("1<<40\0", 1i64 << 40);
    let x: u8 = 200;
    let y: u8 = 100;
    show("x+y wrap\0", x.wrapping_add_demo(y) as i64);
    show("x as i8\0", x as i8 as i64);
    show("-1 as u16\0", -1i32 as u16 as i64);
    show("(-1i8) as u64 > 0\0", ((-1i8) as u64 > 0) as i64);
    show("a < b\0", (a < b) as i64);
    show("u > 3e9\0", (u > 3000000000) as i64);
    show("i8 cmp\0", ((-3i8) < 2i8) as i64);
    show("bits\0", ((0xF0u8 & 0x3C) | 0x01 ^ 0xFF) as i64);
    show("!0u16\0", (!0u16) as i64);
    show("-(-5)\0", -(-5i64));
    let f: f64 = 2.5;
    let g: f64 = 0.5;
    show("f*g*100\0", (f * g * 100.0) as i64);
    show("f/g\0", (f / g) as i64);
    show("f-g\0", (f - g) as i64);
    show("f<g\0", (f < g) as i64);
    show("i to f\0", ((7 as f64) * 1.5) as i64);
    let h: f32 = 3.75;
    show("f32\0", (h * 2.0) as i64);
    show("f32->f64\0", ((h as f64) * 4.0) as i64);
    show("char\0", 'A' as i64);
    show("u8 as char\0", (66u8 as char) as i64);
    show("bool\0", (true as i32 + true as i32) as i64);
    0
}

trait WrapDemo {
    fn wrapping_add_demo(self, other: Self) -> Self;
}
impl WrapDemo for u8 {
    fn wrapping_add_demo(self, other: u8) -> u8 {
        ((self as u32 + other as u32) & 0xFF) as u8
    }
}
