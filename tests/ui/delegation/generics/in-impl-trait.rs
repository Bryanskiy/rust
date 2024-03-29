#![feature(fn_delegation)]

trait GenericTrait<T> {
    fn bar<U>(&self, _: T, _: U) {}
}

mod generic_trait {
    use super::*;

    struct F;
    impl<T> GenericTrait<T> for F {}

    struct S(F);

    impl<A> GenericTrait<A> for S {
        reuse GenericTrait::bar { &self.0 }
    }
}

trait Trait {
    fn foo1(&self) -> i32 { 1 }
    fn foo2<T>(&self, x: T) -> T { x }
}

struct F;
impl Trait for F {}
struct GenericTy<T>(F, T);

mod generic_trait_and_type {
    use super::*;

    impl<A, B> GenericTrait<A> for GenericTy<B> {
        reuse GenericTrait::bar { &self.0 }
    }
}

mod generic_type {
    use super::*;

    impl<T> Trait for GenericTy<T> {
        reuse Trait::{foo1, foo2} { &self.0 }
    }
}

fn main() {}
