#![no_core]
#![feature(no_core, lang_items)]

#[lang = "sized"]
pub trait Sized {}

mod a {
    pub mod b {
        pub fn f() {}
        pub struct S(pub u8);
    }
    pub use self::b::*;
    macro_rules! make_fn {
        ($name:ident) => {
            pub fn $name() {}
        };
    }
    make_fn!(generated);
}

use a::{b::S, f as g};
pub use a::generated;

enum E { A, B(u8), C { x: u8 } }

fn main() {
    let x = 1;
    macro_rules! twice { ($e:expr) => { $e + $e } }
    let y = twice!(x);
    {
        use a::b;
        fn inner() {}
    }
}
