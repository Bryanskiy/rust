#![feature(needs_panic_runtime)]
#![allow(internal_features)]
// We are mock std.
#![no_std]
// Tell rustc to inject panic runtime.
#![needs_panic_runtime]
#![crate_type = "rlib"]
