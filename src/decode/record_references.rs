//! Resolved references belong to one decoder origin and prior table frontier.
use crate::decode::record_schema::Table;
use crate::decode::record_validation::Findings;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Resolved {
    pub table: Table,
    pub slot: u32,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct CheckedShape {
    pub shape: Findings,
    pub missing_reference: bool,
}
