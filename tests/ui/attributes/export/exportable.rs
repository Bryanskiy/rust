#![feature(export)]
#![crate_type="dylib"]

mod m {
    #[export]
    pub struct S;
    //~^ ERROR item with pub(crate) visibility is unexportable

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
