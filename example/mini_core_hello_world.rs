// Adapted from https://github.com/sunfishcode/mir2cranelift/blob/master/rust-examples/nocore-hello-world.rs

#![feature(no_core, unboxed_closures, start, lang_items, box_syntax)]
#![no_core]
#![allow(dead_code)]

extern crate mini_core;

use mini_core::*;

#[link(name = "c")]
extern "C" {
    fn puts(s: *const u8);
}

unsafe extern "C" fn my_puts(s: *const u8) {
    puts(s);
}

// TODO remove when jit supports linking rlibs
#[cfg(jit)]
extern "C" fn panic<T>(_: T) -> ! {
    unsafe {
        intrinsics::abort();
    }
}

#[lang = "termination"]
trait Termination {
    fn report(self) -> i32;
}

impl Termination for () {
    fn report(self) -> i32 {
        unsafe {
            NUM = 6 * 7 + 1 + (1u8 == 1u8) as u8; // 44
            *NUM_REF as i32
        }
    }
}

trait SomeTrait {
    fn object_safe(&self);
}

impl SomeTrait for &'static str {
    fn object_safe(&self) {
        unsafe {
            puts(*self as *const str as *const u8);
        }
    }
}

struct NoisyDrop {
    text: &'static str,
    inner: NoisyDropInner,
}

struct NoisyDropInner;

impl Drop for NoisyDrop {
    fn drop(&mut self) {
        unsafe {
            puts(self.text as *const str as *const u8);
        }
    }
}

impl Drop for NoisyDropInner {
    fn drop(&mut self) {
        unsafe {
            puts("Inner got dropped!\0" as *const str as *const u8);
        }
    }
}

enum Ordering {
    Less = -1,
    Equal = 0,
    Greater = 1,
}

#[lang = "start"]
fn start<T: Termination + 'static>(
    main: fn() -> T,
    _argc: isize,
    _argv: *const *const u8,
) -> isize {
    main().report() as isize
}

static mut NUM: u8 = 6 * 7;
static NUM_REF: &'static u8 = unsafe { &NUM };

macro_rules! assert {
    ($e:expr) => {
        if !$e {
            panic(&(stringify!(! $e), file!(), line!(), 0));
        }
    };
}

macro_rules! assert_eq {
    ($l:expr, $r: expr) => {
        if $l != $r {
            panic(&(stringify!($l != $r), file!(), line!(), 0));
        }
    }
}

struct Unique<T: ?Sized> {
    pointer: *const T,
    _marker: PhantomData<T>,
}

impl<T: ?Sized, U: ?Sized> CoerceUnsized<Unique<U>> for Unique<T> where T: Unsize<U> {}

fn main() {
    unsafe {
        if intrinsics::bitreverse(0b10101000u8) != 0b00010101u8 {
            //intrinsics::abort();
        }
    }
}
