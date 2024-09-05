use run_make_support::{run, rustc};

fn main() {
    rustc().input("lib.rs").run();
}
