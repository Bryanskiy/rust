#![feature(export)]
#![crate_type = "dylib"]

struct Foo;

#[export]
pub extern "C" fn my_foo() -> i16 {
    0i16
}
