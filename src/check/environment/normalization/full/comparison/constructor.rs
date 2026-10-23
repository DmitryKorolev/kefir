//! Pending C10 attempts, scoped to one checked comparison owner.
use super::*;

pub(super) struct Attempt {
    pub incoming: ReductionPath,
    pub prior: Decision,
    pub maximum: ReductionPath,
    pub left_constructor: bool,
}
