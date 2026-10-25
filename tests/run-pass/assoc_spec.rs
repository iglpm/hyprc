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

pub trait MyIter {
    type Item;
}

pub struct MyRange(i64);
impl MyIter for MyRange {
    type Item = i64;
}

pub struct MyList<T>(T);

pub trait MySpecExtend<I> {
    fn my_extend(&mut self, iter: I) -> i64;
}

impl<I: MyIter> MySpecExtend<I> for MyList<I::Item> {
    fn my_extend(&mut self, _iter: I) -> i64 {
        100
    }
}

fn call_extend<T, I: MyIter<Item = T>>(list: &mut MyList<T>, iter: I) -> i64 {
    <MyList<T> as MySpecExtend<I>>::my_extend(list, iter)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut l = MyList(42i64);
    let r = MyRange(10);
    p(call_extend(&mut l, r));
    0
}
