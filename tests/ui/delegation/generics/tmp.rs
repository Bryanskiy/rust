#![feature(fn_delegation)]

trait GenericTrait<T> {
    fn bar<U>(&self, _: T, _: U) {}
}

struct F;
struct GenericTy<T>(F, T);

impl<C> GenericTrait<C> for F {}

impl<A, B> GenericTrait<A> for GenericTy<B> {
    reuse GenericTrait::bar { &self.0 }
}


fn main() {}
