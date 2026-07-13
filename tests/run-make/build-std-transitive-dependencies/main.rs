#![no_std]
#![no_main]
#![allow(unused)]

// Mock std prelude
extern crate mock_std;
use mock_std::*;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    0
}
