//! Private report components; ownership and validation boundaries remain in their owners.
#[cfg(feature = "introspection")]
pub(crate) mod attribution;
pub(crate) mod axiom_report;
pub(crate) mod failure_envelope;
#[cfg(feature = "introspection")]
pub(crate) mod failure_snapshot;
pub(crate) mod report_storage;
