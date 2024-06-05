#![feature(fn_delegation)]
#![allow(incomplete_features)]

mod bounds {
    trait Trait0 {}

    trait Trait1<T> {
        fn foo<U>(&self)
        where
            T: Trait0,
            U: Trait0,
            Self: Trait0,
            //~^ ERROR the trait bound `S: Trait0` is not satisfied
        {
        }
    }

    struct F;
    impl<T> Trait1<T> for F {}

    struct S(F);

    impl<T> Trait1<T> for S {
        reuse Trait1::<T>::foo { &self.0 }
        //~^ ERROR the trait bound `F: Trait0` is not satisfied
    }
}

fn main() {}
