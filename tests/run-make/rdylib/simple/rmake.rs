use run_make_support::{run, rustc};

fn main() {
    rustc().input("libr.rs").arg("-Csymbol-mangling-version=v0").run();

    rustc().input("app.rs").arg("-Csymbol-mangling-version=v0").run();
}
