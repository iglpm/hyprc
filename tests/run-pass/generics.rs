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
trait Shape {
    fn area(&self) -> i64;
    fn name(&self) -> i64 {
        0
    }
    fn double_area(&self) -> i64 {
        self.area() * 2
    }
}

struct Square(i64);
struct Rect {
    w: i64,
    h: i64,
}

impl Shape for Square {
    fn area(&self) -> i64 {
        self.0 * self.0
    }
    fn name(&self) -> i64 {
        1
    }
}

impl Shape for Rect {
    fn area(&self) -> i64 {
        self.w * self.h
    }
}

fn total_area<A: Shape, B: Shape>(a: &A, b: &B) -> i64 {
    a.area() + b.area()
}

fn describe<S>(s: &S) -> i64
where
    S: Shape,
{
    s.name() * 1000 + s.double_area()
}

struct Pair<T> {
    a: T,
    b: T,
}

impl<T: Copy + PartialOrd> Pair<T> {
    fn max(&self) -> T {
        if self.a > self.b { self.a } else { self.b }
    }
}

trait Container {
    type Item;
    fn get(&self, i: usize) -> Self::Item;
    fn first(&self) -> Self::Item {
        self.get(0)
    }
}

struct Three([i64; 3]);

impl Container for Three {
    type Item = i64;
    fn get(&self, i: usize) -> i64 {
        self.0[i]
    }
}

fn sum_container<C: Container<Item = i64>>(c: &C, n: usize) -> i64 {
    let mut s = 0;
    for i in 0..n {
        s += c.get(i);
    }
    s
}

fn identity<T>(x: T) -> T {
    x
}

fn swap<A, B>(p: (A, B)) -> (B, A) {
    (p.1, p.0)
}

trait Zero {
    fn zero() -> Self;
}
impl Zero for i64 {
    fn zero() -> i64 {
        0
    }
}
impl Zero for u8 {
    fn zero() -> u8 {
        0
    }
}

fn zeros<T: Zero>() -> (T, T) {
    (T::zero(), T::zero())
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let s = Square(5);
    let r = Rect { w: 2, h: 7 };
    p(total_area(&s, &r));
    p(describe(&s));
    p(describe(&r));
    let pi = Pair { a: 3, b: 9 };
    p(pi.max() as i64);
    let pf = Pair { a: 2.5f64, b: 1.5 };
    p((pf.max() * 10.0) as i64);
    let pu = Pair { a: 200u8, b: 100u8 };
    p(pu.max() as i64);
    let t = Three([10, 20, 30]);
    p(t.first());
    p(sum_container(&t, 3));
    p(identity(42i64));
    p(identity(7u8) as i64);
    let (x, y) = swap((1i64, 2u8));
    p(x as i64 * 10 + y as i64);
    let (z0, z1): (i64, i64) = zeros();
    p(z0 + z1);
    p(<Square as Shape>::area(&s));
    p(Shape::area(&r));
    0
}
