#!/bin/sh
# Build the wasm32-wasip1 checker with the pinned toolchain and the
# wasm32-wasip1 standard library (`rustup target add wasm32-wasip1`). build.rs passes
# the stack, maximum and initial memory (src/resource/wasm_layout.rs) to the linker;
# this script adds simd128, which every current engine supports.
# Run the result with scripts/wasm/run-wasm.mjs.
set -eu
RUSTFLAGS="-C target-feature=+simd128" \
  exec cargo build --release --locked --target wasm32-wasip1 "$@"
