//@ run-pass
//@ compile-flags: --test
#![feature(fn_delegation)]
#![allow(incomplete_features)]

#[derive(PartialEq, Debug, Copy, Clone)]
struct S<'a, U> {
    x: &'a U
}

trait Trait<T> {
    fn foo<U>(&self, x: U, y: T) -> (T, U) {(y, x)}
}

impl<T> Trait<T> for u8 {}

#[test]
fn check() {
    {
        reuse <u8 as Trait<_>>::foo;
        assert_eq!(foo(&2, "str", 1), (1, "str"));
    }
    {
        reuse <_ as Trait<_>>::foo::<_>;
        assert_eq!(foo(&2, "str", 1), (1, "str"));
    }
}

#[test]
fn check_deep_inf_vars() {
    let x = 0;
    let s = S { x: &x };
    reuse <_ as Trait<S<_>>>::foo;
    assert_eq!(foo(&2, "str", s), (s, "str"));
}
