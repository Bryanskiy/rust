extern dyn crate libr;

fn main() {
    let x = libr::my_foo();
    assert_eq!(x, 0);
}
