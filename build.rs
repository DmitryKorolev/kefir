//! Generates candidate identities, not an identified execution record.
// Shared source is intentional: build scripts are a separate Rust crate.
#[path = "src/identity/mod.rs"]
mod identity;
#[path = "src/resource/profile.rs"]
mod profile;
use identity::{build as build_identity, resource_profile as resource_identity, specification};

use std::{env, fs, path::PathBuf, process::Command};

fn main() {
    // Any failure aborts Cargo's build script; no fallback or placeholder identity.
    // OUT_DIR is Cargo-owned. Supported attribution additionally requires the
    // consumer's fresh target and stable source/dependency/executable checks.
    let root = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("manifest directory"));
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("output directory"));
    // The specification documents, or a root specification.lock without them.
    let selection = specification::select(&root).expect("specification membership");
    if let Some(path) = env::var_os("KEFIR_WRITE_SPECIFICATION_LOCK") {
        let mut lock = Vec::new();
        selection.write_lock(&mut lock).expect("specification lock");
        fs::write(path, lock).expect("write specification lock");
    }
    let inputs =
        build_identity::Inputs::collect(&root, &selection).expect("candidate source membership");
    let mut spec = Vec::new();
    let spec_digest = selection.encode(&mut spec).expect("specification manifest");
    let mut resource = Vec::new();
    let resource_digest = resource_identity::encode(&mut resource).expect("resource manifest");
    let mut test_resource = Vec::new();
    let test_resource_digest =
        resource_identity::encode_batch_test(&mut test_resource).expect("test resource manifest");
    let rustc = env::var_os("RUSTC").expect("compiler path");
    let version = Command::new(rustc)
        .arg("-vV")
        .output()
        .expect("compiler version command");
    assert!(version.status.success(), "compiler version failed");
    assert!(
        compiler_at_least(&version.stdout, (1, 95, 0)),
        "compiler older than the supported minimum"
    );
    let target = env::var("TARGET").expect("Cargo target");
    let profile = env::var("PROFILE").expect("Cargo profile");
    let mut features: Vec<_> = env::vars_os()
        .filter_map(|(key, _)| {
            let key = key.to_str()?;
            key.strip_prefix("CARGO_FEATURE_").map(str::to_owned)
        })
        .collect();
    features.sort_unstable();
    // A final LF distinguishes the empty feature set from a missing setting.
    let features = format!("{}\n", features.join("\n"));
    let mut build = Vec::new();
    let build_digest = inputs
        .encode(
            build_identity::Settings {
                features: features.as_bytes(),
                profile: profile.as_bytes(),
                resource: &resource,
                rustc: &version.stdout,
                specification: &spec,
                target: target.as_bytes(),
            },
            &mut build,
        )
        .expect("candidate build manifest");
    fs::write(out.join("specification.manifest"), spec).expect("write specification");
    fs::write(out.join("resource-profile.manifest"), resource).expect("write resource profile");
    fs::write(out.join("test-resource-profile.manifest"), test_resource)
        .expect("write test resource profile");
    fs::write(out.join("build.manifest"), build).expect("write candidate build");
    // Only emit Rust after all manifests have been written successfully.
    // This source is deterministic from the identified generator and inputs; it
    // is not recursively hashed into its own build-manifest input.
    fs::write(out.join("identities.rs"), format!(
        "pub(crate) const CANDIDATE_IDENTITIES: [[u8; 32]; 3] = [{spec_digest:?}, {build_digest:?}, {resource_digest:?}];\n#[cfg(test)]\n#[allow(dead_code, reason = \"read only by the reduced-profile batch tests\")]\npub(crate) const BATCH_TEST_RESOURCE: [u8; 32] = {test_resource_digest:?};\n"
    )).expect("write candidate constants");
    for key in inputs.files().keys() {
        println!("cargo::rerun-if-changed={key}");
    }
    for key in ["src", "docs/adr", specification::LOCK_FILE] {
        if root.join(key).exists() {
            println!("cargo::rerun-if-changed={key}");
        }
    }
    for key in [
        "RUSTC",
        "TARGET",
        "PROFILE",
        "KEFIR_WRITE_SPECIFICATION_LOCK",
    ] {
        println!("cargo::rerun-if-env-changed={key}");
    }
}

/// Public builds accept any stable compiler at or above the pinned version;
/// `rust-toolchain.toml` still selects the tested version under rustup, and the
/// build identity records the compiler that was actually used.
fn compiler_at_least(version: &[u8], minimum: (u32, u32, u32)) -> bool {
    let Some(rest) = version.strip_prefix(b"rustc ") else {
        return false;
    };
    let mut parts = rest
        .split(|b| matches!(b, b'.' | b' ' | b'-'))
        .map(|part| std::str::from_utf8(part).ok()?.parse::<u32>().ok());
    match (parts.next(), parts.next(), parts.next()) {
        (Some(Some(major)), Some(Some(minor)), Some(Some(patch))) => {
            (major, minor, patch) >= minimum
        }
        _ => false,
    }
}
