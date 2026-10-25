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
fn classify(n: i32) -> i32 {
    match n {
        -2147483648..=-1 => -1,
        0 => 0,
        1 | 2 | 3 => 1,
        4..10 => 2,
        _ => 3,
    }
}

fn collatz(mut n: u64) -> u64 {
    let mut steps = 0;
    while n != 1 {
        n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 };
        steps += 1;
    }
    steps
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // for over a range, with continue and break
    let mut sum = 0;
    for i in 0..20 {
        if i % 3 == 0 {
            continue;
        }
        if i > 15 {
            break;
        }
        sum += i;
    }
    p(sum);
    // loop with a value
    let mut k = 1;
    let v = loop {
        k *= 2;
        if k > 1000 {
            break k;
        }
    };
    p(v);
    // labeled breaks
    let mut count = 0;
    'outer: for a in 0..10 {
        for b in 0..10 {
            if a * b > 20 {
                break 'outer;
            }
            count += 1;
        }
    }
    p(count);
    // labeled block with value
    let x = 'blk: {
        if count > 10 {
            break 'blk 100;
        }
        200
    };
    p(x);
    let ns = [-5, 0, 2, 7, 42];
    for i in 0..5 {
        p(classify(ns[i]) as i64);
    }
    p(collatz(27) as i64);
    // match on tuples, guards, bindings
    let pairs = [(1, 2), (3, 3), (5, 1)];
    for i in 0..3usize {
        let (a, b) = pairs[i];
        let r = match (a, b) {
            (x, y) if x == y => 0,
            (1, y) => y * 10,
            (x, _) => x * 100,
        };
        p(r);
    }
    // if let, while let, let else
    let mut opt = Some(3);
    if let Some(n) = opt {
        p(n);
    }
    let mut counter = 0;
    while let Some(n) = opt {
        counter += n;
        opt = if n > 0 { Some(n - 1) } else { None };
    }
    p(counter);
    let Some(z) = Some(9) else { return 1 };
    p(z);
    // shadowing and blocks
    let s = 5;
    let s = { let t = s * 2; t + 1 };
    p(s);
    0
}
