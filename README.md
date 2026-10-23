# kefir

**K**ernel **E**nforcing **F**ormal **I**nference **R**ules — an independent
external proof checker for Lean 4.

kefir re-checks Lean developments without trusting Lean's own kernel. It reads
declarations exported by [lean4export](https://github.com/leanprover/lean4export)
and checks every type and proof itself, including the inductive types and
recursors, which it re-derives rather than taking from the export.

Each run ends in one of three verdicts:

- **accept**: everything was checked; the report lists every axiom the input
  relies on;
- **reject**: a declaration is wrong;
- **decline**: kefir hit something it doesn't support yet or ran out of its
  resource budget. A decline never claims anything about the proof.

kefir aims to be fast and lean: our goal is to stay on the Pareto frontier of
instructions and peak memory among Lean checkers, on inputs up to Mathlib.

## Build and run

Input is lean4export NDJSON, format 3.1.0. Requires Rust 1.95.0 or newer. Under
rustup, `rust-toolchain.toml` selects 1.95.0, the version kefir is tested and measured
with; the JSON report's build identity records the compiler actually used. Then:

```sh
cargo build --release --locked
IN=/path/to/export.ndjson ./target/release/kefir
```

For a build tuned to the machine it runs on, as in the Lean Kernel Arena entry, use
`RUSTFLAGS="-C target-cpu=native" cargo build --release --locked`. Native code
generation changes no outcome or resource accounting.

Exit codes: 0 accept, 1 reject, 2 decline, 3 input error or internal failure.
The JSON report distinguishes the latter two. Optional axiom policy arguments:
`--axiom-policy=exclude-native-marked` and
`--axiom-policy=allow-all-declared-axioms`. The policy and assumed axioms must be
considered when interpreting acceptance.

## Resource limits

Resource budgets are part of checking and are fixed in this release. Exhausting a budget
declines; it never produces a verdict.

- **Stack:** checking runs on one thread with a 2 GiB stack reservation. This is address
  space, used only as deep recursion needs it. The evaluator tracks its own stack use and
  gives up an attempt before the end of the reservation.
- **Storage:** up to 16 GiB of managed live storage, plus fixed limits on input size,
  record size, nesting depth and charged work.
- **Measured peak memory** on the Lean Kernel Arena libraries: about 2.5 GB on Mathlib,
  at most about 1.1 GB on the others.

Overflow checks stay enabled in release builds.

## License

Licensed under the Apache License, Version 2.0. See LICENSE. Third-party notices do not specify the license of kefir itself.
