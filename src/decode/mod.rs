//! Private decode components; ownership and validation boundaries remain in their owners.
pub(crate) mod export_header;
pub(crate) mod framing;
pub(crate) mod identifiers;
pub(crate) mod primitive_decode;
pub(crate) mod record_references;
pub(crate) mod record_schema;
pub(crate) mod record_validation;
