//! Fixed derived quotient signatures. No generated syntax is retained here.
use super::*;
use std::num::NonZeroU8;
pub(super) mod schema;

#[derive(Clone, Copy)]
pub(super) struct Package {
    pub names: [NameId; 7],
    pub seen: NonZeroU8,
}
const _: () = assert!(size_of::<Option<Package>>() == 32);
impl QuotientRole {
    pub(super) const fn index(self) -> usize {
        match self {
            Self::Type => 0,
            Self::Constructor => 1,
            Self::Lift => 2,
            Self::Induction => 3,
        }
    }
    pub(super) const fn mask(self) -> u8 {
        1 << self.index()
    }
    pub(super) const fn arity(self) -> usize {
        if matches!(self, Self::Lift) { 2 } else { 1 }
    }
}
impl Environment {
    /// Caller has completely checked this derived schema in the supplied private
    /// phase. Its root is session scratch and intentionally is not an argument.
    /// Only the role and persistent names survive; no reduction authority does.
    pub(super) fn stage_quotient(
        &mut self,
        phase: Formation,
        role: QuotientRole,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Formation, ResourceError> {
        self.check_visibility(phase.before(), Some(phase))?;
        let old = self.stage.ok_or(ResourceError::Invariant)?;
        let package = self.quotient.ok_or(ResourceError::Invariant)?;
        let mut next = self.next_phase(self.entries.len())?;
        self.stage = Some(Stage { phase: next, ..old });
        self.append_entry(
            &ConstantSignature {
                slot: None,
                kind: StoredKind::Quotient(role),
                name: package.names[role.index() + 1],
                parameters: &package.names[5..5 + role.arity()],
                ty: TypeSource::Quotient(role),
                value: None,
                all: &[],
                safety: Safety::Safe,
                hint: None,
            },
            names,
            budget,
        )?;
        next.before = u32::try_from(self.entries.len()).map_err(|_| ResourceError::Counter)?;
        self.stage = Some(Stage { phase: next, ..old });
        Ok(next)
    }
    /// All schemas and the first descriptor matched and every checking session
    /// retired. Preparation may fail; publication through the token cannot.
    pub(super) fn prepare_quotient_commit(
        &mut self,
        phase: Formation,
        budget: &mut Budget,
    ) -> Result<PreparedCommit<'_>, ResourceError> {
        self.check_visibility(phase.before(), Some(phase))?;
        self.require_public_stage()?;
        budget.charge_work(5)?;
        if self.quotient.is_none() || self.entries.len().checked_sub(self.len()) != Some(4) {
            return Err(ResourceError::Invariant);
        }
        for (entry, role) in self.entries[self.len()..].iter().zip([
            QuotientRole::Type,
            QuotientRole::Constructor,
            QuotientRole::Lift,
            QuotientRole::Induction,
        ]) {
            if entry.kind != StoredKind::Quotient(role) {
                return Err(ResourceError::Invariant);
            }
        }
        Ok(PreparedCommit {
            environment: self,
            natural: natural::Certificate::default(),
        })
    }
}
