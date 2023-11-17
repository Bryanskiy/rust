// run-pass

mod simple {
    struct F;

    impl F {
        fn foo_ref(&self, x: i32, y: i32) -> i32 { x }
        fn bar_ref(&self) -> i32 { 42 }
    }

    struct S(F);

    impl S {
        override foo_ref(&self) { self.0 }
        override bar_ref as bar_ref_renamed { self.0 }
    }

    pub fn test() {
        let s = S(F);
        assert_eq!(1, s.foo_ref(1, 2));
        assert_eq!(42, s.bar_ref_renamed());
    }
}

mod generics_types {
    // TODO: compiler/rustc_resolve/src/lib.rs:1134:9

    struct F;
    impl F {
        fn bar<T>(&self, x: T) -> T { x }
    }

    struct S(F);
    impl S {
        override bar { self.0 }
    }

    pub fn test() {
        let s = S(F);
        assert_eq!(42, s.bar(42));
    }
}

fn main() {
    simple::test();
    generics_types::test();
}
