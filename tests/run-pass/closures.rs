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
fn apply<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 {
    f(x)
}

fn apply_twice<F>(mut f: F) -> i64
where
    F: FnMut() -> i64,
{
    f();
    f()
}

fn consume<F: FnOnce() -> i64>(f: F) -> i64 {
    f()
}

fn compose<F: Fn(i64) -> i64, G: Fn(i64) -> i64>(f: F, g: G, x: i64) -> i64 {
    g(f(x))
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let k = 10;
    let add_k = |x| x + k;
    p(add_k(5));
    p(apply(add_k, 1));
    p(apply(|x| x * x, 9));
    let mut counter = 0;
    let n = apply_twice(|| {
        counter += 1;
        counter * 100
    });
    p(n);
    p(counter);
    let owned = Pair2 { a: 3, b: 4 };
    let s = consume(move || owned.a * owned.b);
    p(s);
    p(compose(|x| x + 1, |x| x * 2, 5));
    let mul = |a: i64, b: i64| -> i64 { a * b };
    p(mul(6, 7));
    let nested = |x: i64| {
        let inner = |y: i64| y + x;
        inner(x)
    };
    p(nested(21));
    let mut acc = 0;
    for i in 0..5 {
        let mut add = |v: i64| acc += v;
        add(i);
    }
    p(acc);
    0
}

struct Pair2 {
    a: i64,
    b: i64,
}
