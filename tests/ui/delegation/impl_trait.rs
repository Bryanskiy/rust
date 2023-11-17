// run-pass

mod simple {
    struct F;

    trait Trait {
        fn foo(&self, x: i32, y: i32) -> i32;
        fn bar(&mut self, _x: i32) -> i32 { 42 }
    }

    impl Trait for F {
        fn foo(&self, x: i32, _y: i32) -> i32 { x }
    }

    struct S(F);

    impl Trait for S {
        override foo, bar { self.0 }
    }

    pub fn test() {
        let mut s = S(F);
        assert_eq!(42, s.bar(1));
        assert_eq!(40, s.foo(40, 42));
    }
}

mod lifetimes {
    use std::fmt;

    struct ErrorTy;

    impl ErrorTy {
        fn description(&self) -> &str {
            "ErrorTy"
        }
    }

    impl fmt::Display for ErrorTy {
        override fmt { self.description() }
    }

    pub fn test() {
        assert_eq!("ErrorTy", format!("{ErrorTy}"));
    }
}

mod generic_types {
    struct F;
    trait Trait {
        fn bar<T>(&self, x: T) -> T { x }
    }
    impl Trait for F {}

    struct S(F);
    impl Trait for S {
        override bar { self.0 }
    }

    pub fn test() {
        let s = S(F);
        assert_eq!(42, s.bar(42));
    }
}

mod predicates {
    use std::hash;

    pub struct NonNull<T: ?Sized> {
        pointer: *const T,
    }

    impl<T: ?Sized> NonNull<T> {
        pub const fn as_ptr(&self) -> *mut T {
            self.pointer as *mut T
        }
    }

    impl<T: ?Sized> hash::Hash for NonNull<T> {
        // fn hash<H: hash::Hasher>(&self, state: &mut H) {
        //     self.as_ptr().hash(state)
        // }

        override hash { self.as_ptr() }
    }

    pub fn test() {
        // todo
    }
}

fn main() {
    simple::test();
    lifetimes::test();
    generic_types::test();
    predicates::test();
}
