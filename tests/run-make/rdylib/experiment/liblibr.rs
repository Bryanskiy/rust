#![feature(prelude_import)]
#![no_std]
#![feature(export)]
#![crate_type = "dylib"]
#[prelude_import]
pub use ::std::prelude::rust_2015::*;
#[macro_use]
pub extern crate std;
pub struct Foo;
#[export]
pub extern "C" fn my_foo() -> i16 { loop {} } 
