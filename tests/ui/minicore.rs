//! A minimal core for `#![no_core]` test programs: the lang items rustc and hyprc need to
//! compile them, and impls for the primitive operations the tests use.

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
#[lang = "clone"]
pub trait Clone: Sized {
    fn clone(&self) -> Self;
}
#[lang = "freeze"]
pub unsafe auto trait Freeze {}
#[lang = "sync"]
pub unsafe auto trait Sync {}

#[lang = "panic_location"]
pub struct Location<'a> {
    file: &'a str,
    line: u32,
    col: u32,
}

#[lang = "unsize"]
pub trait Unsize<T: PointeeSized>: PointeeSized {}
#[lang = "coerce_unsized"]
pub trait CoerceUnsized<T> {}
impl<'a, T: PointeeSized + Unsize<U>, U: PointeeSized> CoerceUnsized<&'a U> for &'a T {}
impl<'a, T: PointeeSized + Unsize<U>, U: PointeeSized> CoerceUnsized<&'a mut U> for &'a mut T {}
impl<T: PointeeSized + Unsize<U>, U: PointeeSized> CoerceUnsized<*const U> for *const T {}
impl<T: PointeeSized + Unsize<U>, U: PointeeSized> CoerceUnsized<*mut U> for *mut T {}

#[lang = "destruct"]
pub trait Destruct: PointeeSized {}

#[lang = "drop_glue"]
pub unsafe fn drop_glue<T: PointeeSized>(_: &mut T) {}

#[lang = "legacy_receiver"]
pub trait LegacyReceiver {}
impl<T: PointeeSized> LegacyReceiver for &T {}
impl<T: PointeeSized> LegacyReceiver for &mut T {}

macro_rules! impl_copy {
    ($($t:ty)*) => { $(impl Copy for $t {} impl Clone for $t { fn clone(&self) -> Self { *self } })* };
}
impl_copy!(bool char u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);
impl<T: PointeeSized> Copy for *const T {}
impl<T: PointeeSized> Copy for *mut T {}
impl<T: PointeeSized> Copy for &T {}
impl<T: PointeeSized> Clone for *const T { fn clone(&self) -> Self { *self } }
impl<T: PointeeSized> Clone for *mut T { fn clone(&self) -> Self { *self } }
impl<T: PointeeSized> Clone for &T { fn clone(&self) -> Self { *self } }
impl<T: Copy, const N: usize> Copy for [T; N] {}
impl<T: Copy, const N: usize> Clone for [T; N] { fn clone(&self) -> Self { *self } }

macro_rules! binop {
    ($lang:literal $Trait:ident $method:ident $op:tt; $($t:ty)*) => {
        #[lang = $lang]
        pub trait $Trait<Rhs = Self> {
            type Output;
            fn $method(self, rhs: Rhs) -> Self::Output;
        }
        $(impl $Trait for $t {
            type Output = $t;
            fn $method(self, rhs: $t) -> $t { self $op rhs }
        })*
    };
}
binop!("add" Add add +; u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);
binop!("sub" Sub sub -; u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);
binop!("mul" Mul mul *; u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);
binop!("div" Div div /; u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);
binop!("rem" Rem rem %; u8 u16 u32 u64 usize i8 i16 i32 i64 isize);
binop!("bitand" BitAnd bitand &; bool u8 u16 u32 u64 usize i8 i16 i32 i64 isize);
binop!("bitor" BitOr bitor |; bool u8 u16 u32 u64 usize i8 i16 i32 i64 isize);
binop!("bitxor" BitXor bitxor ^; bool u8 u16 u32 u64 usize i8 i16 i32 i64 isize);

macro_rules! shiftop {
    ($lang:literal $Trait:ident $method:ident $op:tt; $($t:ty)*) => {
        #[lang = $lang]
        pub trait $Trait<Rhs = Self> {
            type Output;
            fn $method(self, rhs: Rhs) -> Self::Output;
        }
        $(impl $Trait<i32> for $t {
            type Output = $t;
            fn $method(self, rhs: i32) -> $t { self $op rhs }
        })*
    };
}
shiftop!("shl" Shl shl <<; u8 u16 u32 u64 usize i8 i16 i32 i64 isize);
shiftop!("shr" Shr shr >>; u8 u16 u32 u64 usize i8 i16 i32 i64 isize);

macro_rules! assignop {
    ($lang:literal $Trait:ident $method:ident $op:tt; $($t:ty)*) => {
        #[lang = $lang]
        pub trait $Trait<Rhs = Self> {
            fn $method(&mut self, rhs: Rhs);
        }
        $(impl $Trait for $t {
            fn $method(&mut self, rhs: $t) { *self = *self $op rhs; }
        })*
    };
}
assignop!("add_assign" AddAssign add_assign +; u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);
assignop!("sub_assign" SubAssign sub_assign -; u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);
assignop!("mul_assign" MulAssign mul_assign *; u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);

#[lang = "neg"]
pub trait Neg {
    type Output;
    fn neg(self) -> Self::Output;
}
macro_rules! neg {
    ($($t:ty)*) => { $(impl Neg for $t { type Output = $t; fn neg(self) -> $t { -self } })* };
}
neg!(i8 i16 i32 i64 isize f32 f64);

#[lang = "not"]
pub trait Not {
    type Output;
    fn not(self) -> Self::Output;
}
macro_rules! not {
    ($($t:ty)*) => { $(impl Not for $t { type Output = $t; fn not(self) -> $t { !self } })* };
}
not!(bool u8 u16 u32 u64 usize i8 i16 i32 i64 isize);

#[lang = "eq"]
pub trait PartialEq<Rhs: PointeeSized = Self>: PointeeSized {
    fn eq(&self, other: &Rhs) -> bool;
    fn ne(&self, other: &Rhs) -> bool { !self.eq(other) }
}
#[lang = "partial_ord"]
pub trait PartialOrd<Rhs: PointeeSized = Self>: PartialEq<Rhs> + PointeeSized {
    fn lt(&self, other: &Rhs) -> bool;
    fn le(&self, other: &Rhs) -> bool;
    fn gt(&self, other: &Rhs) -> bool;
    fn ge(&self, other: &Rhs) -> bool;
}
macro_rules! cmp {
    ($($t:ty)*) => { $(
        impl PartialEq for $t { fn eq(&self, other: &$t) -> bool { *self == *other } }
        impl PartialOrd for $t {
            fn lt(&self, other: &$t) -> bool { *self < *other }
            fn le(&self, other: &$t) -> bool { *self <= *other }
            fn gt(&self, other: &$t) -> bool { *self > *other }
            fn ge(&self, other: &$t) -> bool { *self >= *other }
        }
    )* };
}
cmp!(bool char u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);

#[lang = "drop"]
pub trait Drop {
    fn drop(&mut self);
}

pub mod libc {
    unsafe extern "C" {
        pub fn printf(fmt: *const u8, ...) -> i32;
        pub fn puts(s: *const u8) -> i32;
        pub fn malloc(size: usize) -> *mut u8;
        pub fn free(p: *mut u8);
        pub fn abort() -> !;
    }
}

#[lang = "tuple_trait"]
pub trait Tuple {}

#[lang = "fn_once"]
#[rustc_paren_sugar]
pub trait FnOnce<Args: Tuple> {
    #[lang = "fn_once_output"]
    type Output;
    extern "rust-call" fn call_once(self, args: Args) -> Self::Output;
}
#[lang = "fn_mut"]
#[rustc_paren_sugar]
pub trait FnMut<Args: Tuple>: FnOnce<Args> {
    extern "rust-call" fn call_mut(&mut self, args: Args) -> Self::Output;
}
#[lang = "fn"]
#[rustc_paren_sugar]
pub trait Fn<Args: Tuple>: FnMut<Args> {
    extern "rust-call" fn call(&self, args: Args) -> Self::Output;
}

#[lang = "Option"]
pub enum Option<T> {
    #[lang = "None"]
    None,
    #[lang = "Some"]
    Some(T),
}
pub use Option::{None, Some};

impl<T> Option<T> {
    pub fn is_some(&self) -> bool {
        match self {
            Some(_) => true,
            None => false,
        }
    }
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Some(x) => x,
            None => default,
        }
    }
}

#[lang = "iterator"]
pub trait Iterator {
    type Item;
    #[lang = "next"]
    fn next(&mut self) -> Option<Self::Item>;
}

pub trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;
    #[lang = "into_iter"]
    fn into_iter(self) -> Self::IntoIter;
}

impl<I: Iterator> IntoIterator for I {
    type Item = I::Item;
    type IntoIter = I;
    fn into_iter(self) -> I {
        self
    }
}

#[lang = "Range"]
pub struct Range<Idx> {
    pub start: Idx,
    pub end: Idx,
}

pub trait Step: Sized + Copy + PartialOrd + Add<Output = Self> {
    fn one() -> Self;
}
macro_rules! step {
    ($($t:ty)*) => { $(impl Step for $t { fn one() -> $t { 1 } })* };
}
step!(u8 u16 u32 u64 usize i8 i16 i32 i64 isize);

impl<A: Step> Iterator for Range<A> {
    type Item = A;
    fn next(&mut self) -> Option<A> {
        if self.start < self.end {
            let v = self.start;
            self.start = v + A::one();
            Some(v)
        } else {
            None
        }
    }
}

#[lang = "index"]
pub trait Index<Idx> {
    type Output: ?Sized;
    fn index(&self, index: Idx) -> &Self::Output;
}
#[lang = "index_mut"]
pub trait IndexMut<Idx>: Index<Idx> {
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
impl<T> Index<usize> for [T] {
    type Output = T;
    fn index(&self, i: usize) -> &T { &self[i] }
}
impl<T> IndexMut<usize> for [T] {
    fn index_mut(&mut self, i: usize) -> &mut T { &mut self[i] }
}
impl<T, const N: usize> Index<usize> for [T; N] {
    type Output = T;
    fn index(&self, i: usize) -> &T { &self[i] }
}
impl<T, const N: usize> IndexMut<usize> for [T; N] {
    fn index_mut(&mut self, i: usize) -> &mut T { &mut self[i] }
}


#[rustc_builtin_macro]
pub macro stringify($($t:tt)*) {
    /* compiler built-in */
}

pub mod panicking {
    use super::stringify;
    macro_rules! panic_const {
        ($($lang:ident = $msg:literal,)*) => { $(
            #[lang = stringify!($lang)]
            pub fn $lang() -> ! {
                unsafe {
                    super::libc::printf("panicked: %s\n\0" as *const str as *const u8, $msg as *const str as *const u8);
                    super::libc::abort()
                }
            }
        )* };
    }
    panic_const! {
        panic_const_add_overflow = "attempt to add with overflow\0",
        panic_const_sub_overflow = "attempt to subtract with overflow\0",
        panic_const_mul_overflow = "attempt to multiply with overflow\0",
        panic_const_div_overflow = "attempt to divide with overflow\0",
        panic_const_rem_overflow = "attempt to calculate the remainder with overflow\0",
        panic_const_neg_overflow = "attempt to negate with overflow\0",
        panic_const_shr_overflow = "attempt to shift right with overflow\0",
        panic_const_shl_overflow = "attempt to shift left with overflow\0",
        panic_const_div_by_zero = "attempt to divide by zero\0",
        panic_const_rem_by_zero = "attempt to calculate the remainder with a divisor of zero\0",
    }

    #[lang = "panic_bounds_check"]
    pub fn panic_bounds_check(index: usize, len: usize) -> ! {
        unsafe {
            super::libc::printf("panicked: index out of bounds: the len is %zu but the index is %zu\n\0" as *const str as *const u8, len, index);
            super::libc::abort()
        }
    }
}
