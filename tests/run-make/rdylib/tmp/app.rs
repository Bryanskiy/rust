#[link(name = "lib_tmp")]
extern "C" {
    fn foo();
}

fn main() {
    unsafe {
        foo();
    }
}
