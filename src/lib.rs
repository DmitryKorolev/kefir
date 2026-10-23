//! Independent checking of the supported lean4export subset, with bounded reports.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Outcome {
    Accept,
    Reject,
    Decline,
    InputError,
    InternalError,
}
// Introspection diagnostics must never change an outcome.
// std's eprintln! panics when stderr cannot be written, which would turn a
// verdict into an internal panic. In introspection builds this crate-wide
// shadow writes the same text and ignores write failures. It is defined
// before every module so its textual scope covers the whole crate, and it
// keeps diagnostic source text, which experiment scripts patch by anchor,
// unchanged.
#[cfg(feature = "introspection")]
macro_rules! eprintln {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

mod run;
pub use run::{AxiomPolicy, InputError, Run};
mod candidate_identity {
    include!(concat!(env!("OUT_DIR"), "/identities.rs"));
}

mod check;
mod decode;
mod report;
mod resource;
mod syntax;
