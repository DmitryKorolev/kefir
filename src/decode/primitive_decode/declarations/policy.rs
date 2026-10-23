//! Visible axiom exclusions. No typing, installation or verdict.
use super::{Kind, Request};
use crate::resource::{Budget, ResourceError};
use crate::syntax::names::{Component, Names};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Marker {
    Clear,
    Excluded,
}

impl Request<'_> {
    /// Call after complete structural record validation, for EVERY axiom,
    /// including unused ones and those following a pending semantic negative.
    /// Excluded means support.policy, never ill-typed. Clear grants no checkedness.
    /// The request and Names must share their originating decoder; names are
    /// immutable, prior-prefix DAG nodes, so this walk terminates without recursion.
    /// No cache/allocation: one charged view per component, O(depth + payload bytes)
    /// work and constant stack space; no per-node or per-declaration retained cost.
    pub(crate) fn axiom_marker(
        &self,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Marker, ResourceError> {
        b.charge_work(1)?;
        if self.kind != Kind::Axiom {
            return Ok(Marker::Clear);
        }
        let mut current = self.name;
        while let Some((prefix, component)) = names.view(current, b)? {
            if matches!(component, Component::String("_native")) {
                return Ok(Marker::Excluded);
            }
            current = prefix;
        }
        // A clear marker grants no authority: all axioms, including the three
        // legacy Lean names, still require ordinary validation and reporting.
        Ok(Marker::Clear)
    }
}
