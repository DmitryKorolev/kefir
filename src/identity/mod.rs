//! Build-time identity generation, shared with its integration tests.
//! This module is not linked into the production checker.
pub(crate) mod build;
pub(crate) mod manifest;
pub(crate) mod resource_profile;
pub(crate) mod sha256;
pub(crate) mod specification;
