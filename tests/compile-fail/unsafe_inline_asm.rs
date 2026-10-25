#![feature(no_core, lang_items, auto_traits, rustc_attrs, unboxed_closures, intrinsics, decl_macro)]
#![allow(internal_features, unused)]
#![no_core]

#[path = "../ui/minicore.rs"]
mod minicore;
use minicore::*;

#[rustc_builtin_macro]
macro asm($($tokens:tt)*) {}

fn safe_function() {
    asm!("nop");
}
