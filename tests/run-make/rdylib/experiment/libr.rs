#![feature(export)]
#![crate_type = "rdylib"]

#[export]
pub extern "C" fn my_foo() -> i16 {
    0i16
}
