//@ run-pass

#![feature(fn_delegation)]
#![allow(incomplete_features)]
#![allow(dead_code)]

trait Trait1 {
    fn foo(&self) -> i32 { 1 }
}

trait Trait2 {
    fn foo(&self) -> i32 { 2 }
}

struct F;
impl Trait1 for F {}
impl Trait2 for F {}

impl F {
    fn foo(&self) -> i32 { 3 }
}

struct S(F);

impl Trait1 for S {
    reuse Trait1::foo { self.0 }
}

fn main() {
    let s = S(F);
    assert_eq!(s.foo(), 1);
}
