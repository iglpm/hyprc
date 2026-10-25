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
struct Vec2 {
    x: i32,
    y: i32,
}

impl Copy for Vec2 {}
impl Clone for Vec2 {
    fn clone(&self) -> Vec2 {
        *self
    }
}

impl Vec2 {
    fn new(x: i32, y: i32) -> Self {
        Vec2 { x, y }
    }
    fn dot(self, o: Vec2) -> i32 {
        self.x * o.x + self.y * o.y
    }
    fn scale(&mut self, k: i32) {
        self.x *= k;
        self.y *= k;
    }
}

struct Wrapper(u64, bool);

enum Expr {
    Num(i64),
    Add(i64, i64),
    Neg { value: i64 },
    Nothing,
}

fn eval(e: &Expr) -> i64 {
    match *e {
        Expr::Num(n) => n,
        Expr::Add(a, b) => a + b,
        Expr::Neg { value } => -value,
        Expr::Nothing => 0,
    }
}

enum Tree {
    Leaf(i32),
    Node(i32, i32, i32),
}

fn depth_sum(t: &Tree) -> i32 {
    match t {
        Tree::Leaf(v) => *v,
        Tree::Node(a, b, c) => *a + *b + *c,
    }
}

#[repr(u8)]
enum Color {
    Red = 1,
    Green = 4,
    Blue = 9,
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = Vec2::new(3, 4);
    let b = Vec2 { x: 1, ..a };
    p(a.dot(b) as i64);
    a.scale(10);
    p(a.x as i64);
    p(a.y as i64);
    let w = Wrapper(77, true);
    p(w.0 as i64);
    p(w.1 as i64);
    let exprs = [Expr::Num(5), Expr::Add(2, 3), Expr::Neg { value: 8 }, Expr::Nothing];
    let total = exprs_array(exprs);
    p(total[3] as i64);
    let e1 = Expr::Add(40, 2);
    p(eval(&e1));
    p(eval(&Expr::Neg { value: 5 }));
    p(eval(&Expr::Nothing));
    let t = Tree::Node(1, 2, 3);
    p(depth_sum(&t) as i64);
    p(depth_sum(&Tree::Leaf(9)) as i64);
    p(Color::Green as i64);
    p(Color::Blue as u8 as i64);
    // Option of a reference uses the null niche.
    let r = &a;
    let o: Option<&Vec2> = Some(r);
    match o {
        Some(v) => p(v.x as i64),
        None => p(-1),
    }
    let n: Option<&Vec2> = None;
    p(n.is_some() as i64);
    let ob: Option<bool> = Some(false);
    match ob {
        Some(true) => p(1),
        Some(false) => p(2),
        None => p(3),
    }
    let nested = Some(Some(5));
    if let Some(Some(x)) = nested {
        p(x);
    }
    0
}

fn exprs_array(e: [Expr; 4]) -> [i32; 4] {
    [1, 2, 3, 4]
}
