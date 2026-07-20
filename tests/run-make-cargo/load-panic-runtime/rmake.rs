//@ needs-target-std

use run_make_support::{cargo, path, target};

fn main() {
    let target_dir = path("target");

    cargo()
        .args(&[
            "build",
            "--release",
            "--manifest-path",
            "Cargo.toml",
            "-Zbuild-std=std",
            "--target",
            &target(),
        ])
        .env("RUSTC_BOOTSTRAP", "1")
        // Visual Studio 2022 requires that the LIB env var be set so it can
        // find the Windows SDK.
        .env("LIB", std::env::var("LIB").unwrap_or_default())
        .run_fail()
        .assert_stderr_contains("multiple candidates for `rlib` dependency `panic_abort` found");
}
