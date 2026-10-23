//! Private check components; ownership and validation boundaries remain in their owners.
pub(crate) mod environment;
pub(crate) mod natural;
pub(crate) mod theorem_copy;

pub(crate) mod delayed;

#[cfg(feature = "introspection")]
pub(crate) mod diagnostic;
