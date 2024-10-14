#![allow(incomplete_features)]
#![feature(export)]
#![feature(inherent_associated_types)]
#![crate_type="lib"]

mod m {
    #[export]
    pub struct S;
    //~^ ERROR item with pub(crate) visibility is unexportable
    //~| ERROR type without stable representation is unexportable

    pub fn foo() {}
    //~^ ERROR non "C" ABI function is unexportable
}

#[export]
pub use m::foo;

#[export]
pub mod m1 {
    #[repr(C)]
    pub struct S1; // OK, public type with stable repr

    struct S2;
    //~^ ERROR type without stable representation is unexportable
}

pub mod fn_sig {
    #[export]
    pub fn foo1() {}
    //~^ ERROR non "C" ABI function is unexportable

    #[export]
    #[repr(C)]
    pub struct S;

    #[export]
    pub extern "C" fn foo2(x: S) {}

    #[export]
    pub extern "C" fn foo3(x: Box<S>) {}
    //~^ ERROR fn with not exportable nested type is unexportable
}

pub mod impl_item {
    pub struct S;

    impl S {
        #[export]
        pub extern "C" fn foo1(&self) {}

        #[export]
        pub extern "C" fn foo2(self) {}
        //~^ ERROR fn with not exportable nested type is unexportable
    }

    pub struct S2<T>(T);

    impl<T> S2<T> {
        #[export]
        pub extern "C" fn foo1(&self) {}
        //~^ ERROR generic item is unexportable
    }
}

pub mod type_aliases {
    trait Trait {
        type Type;
    }
    pub struct S;

    impl Trait for S {
        type Type = (u32,);
    }

    #[export]
    pub extern "C" fn foo1(x: <S as Trait>::Type) {}
    //~^ ERROR (u32,) is unexportable

    #[export]
    pub type Type = [i32; 4];
    //~^ ERROR [i32; 4] is unexportable

    impl S {
        #[export]
        pub type Type = extern "C" fn();
        //~^ ERROR extern "C" fn() is unexportable
        // FIXME: wrong error message
        //~| ERROR () is unexportable
    }
}
