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

mod generics {
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

    // TODO: library/core/src/ptr/non_null.rs:765:9
}

fn main() {
    simple::test();
    generics::test();
}
