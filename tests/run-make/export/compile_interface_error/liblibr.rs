#![feature(prelude_import)]
#![no_std]
#![feature(export)]
#![crate_type = "sdylib"]

// interface file is broken:
#[export]
pub extern "C" fn foo()
