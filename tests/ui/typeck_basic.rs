#![feature(no_core, lang_items, auto_traits, rustc_attrs, unboxed_closures, intrinsics, decl_macro)]
#![allow(internal_features, unused)]
#![no_core]
#![no_main]

#[path = "minicore.rs"]
mod minicore;
use minicore::*;

extern "C" {
    fn printf(fmt: *const u8, ...) -> i32;
}

fn fib(n: u64) -> u64 {
    if n < 2 { n } else { fib(n - 1) + fib(n - 2) }
}

struct Point {
    x: i32,
    y: i32,
}

impl Point {
    fn new(x: i32, y: i32) -> Point {
        Point { x, y }
    }

    fn sum(&self) -> i32 {
        self.x + self.y
    }
}

enum Shape {
    Circle(i32),
    Rect { w: i32, h: i32 },
    Empty,
}

fn area(s: &Shape) -> i32 {
    match s {
        Shape::Circle(r) => 3 * *r * *r,
        Shape::Rect { w, h } => *w * *h,
        Shape::Empty => 0,
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let p = Point::new(1, 2);
    let s = p.sum();
    let shapes = (Shape::Circle(2), Shape::Rect { w: 3, h: 4 }, Shape::Empty);
    let mut total = area(&shapes.0) + area(&shapes.1) + area(&shapes.2);
    let mut i = 0;
    while i < 3 {
        total += 1;
        i += 1;
    }
    unsafe {
        printf("fib(30) = %d, sum = %d, total = %d\n\0" as *const str as *const u8, fib(30) as i32, s, total);
    }
    0
}
