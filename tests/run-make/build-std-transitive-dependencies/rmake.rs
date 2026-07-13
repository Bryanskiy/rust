use run_make_support::{path, rfs, rust_lib_name, rustc};

fn main() {
    rfs::create_dir("panic_abort");
    rfs::create_dir("mock_std");

    // Compile `panic_abort` and put it in a separate directory.
    rustc().input("mock-std/panic_abort.rs").run();
    let panic_abort_path = path("panic_abort").join(rust_lib_name("panic_abort"));
    rfs::rename(rust_lib_name("panic_abort"), &panic_abort_path);

    // Compile `mock_std` and put it in a separate directory.
    rustc()
        .input("mock-std/mock_std.rs")
        .extern_("panic_abort", &panic_abort_path)
        .run();
    let mock_std_path = path("mock_std").join(rust_lib_name("mock_std"));
    rfs::rename(rust_lib_name("mock_std"), &mock_std_path);

    // Compile final artifact.
    rustc()
        .input("main.rs")
        .arg("-Cpanic=abort")
        .extern_("mock_std", &mock_std_path)
        .library_search_path(format!("dependency={}", path("panic_abort").display()))
        .run();
}
