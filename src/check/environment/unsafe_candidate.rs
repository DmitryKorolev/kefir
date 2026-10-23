//! Validator-only full unsafe-definition candidate transaction.
use super::*;

impl Environment {
    /// Header checking and its session cleanup have succeeded in the prior
    /// environment. No other staged entry exists. The returned phase is usable
    /// only by this candidate's unsafe body session; check_use enforces safety.
    pub(super) fn stage_unsafe_candidate(
        &mut self,
        request: &Request<'_>,
        expression_end: usize,
        level_end: usize,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Formation, ResourceError> {
        if request.kind != Kind::Definition
            || request.safety != Safety::Unsafe
            || request.value.is_none()
            || request.ty.slot() as usize >= expression_end
            || request
                .value
                .is_some_and(|v| v.slot() as usize >= expression_end)
        {
            return Err(ResourceError::Invariant);
        }
        let phase = self.begin_stage(expression_end, level_end, budget)?;
        self.append_entry(
            &ConstantSignature {
                slot: None,
                kind: StoredKind::Ordinary(Kind::Definition),
                name: request.name,
                parameters: request.parameters,
                ty: TypeSource::Original(request.ty),
                value: request.value,
                all: request.all,
                safety: Safety::Unsafe,
                hint: request.hint,
            },
            names,
            budget,
        )?;
        let next = self.next_phase(self.entries.len())?;
        let stage = self.stage.ok_or(ResourceError::Invariant)?;
        if stage.phase != phase {
            return Err(ResourceError::Invariant);
        }
        self.stage = Some(Stage {
            phase: next,
            ..stage
        });
        Ok(next)
    }

    /// Body inference/comparison and the candidate session's retirement have
    /// succeeded. Only this single full candidate may become committed.
    pub(super) fn prepare_unsafe_commit(
        &mut self,
        phase: Formation,
        budget: &mut Budget,
    ) -> Result<PreparedCommit<'_>, ResourceError> {
        self.check_visibility(phase.before(), Some(phase))?;
        self.require_public_stage()?;
        budget.charge_work(1)?;
        let [entry] = &self.entries[self.len()..] else {
            return Err(ResourceError::Invariant);
        };
        if entry.kind != StoredKind::Ordinary(Kind::Definition)
            || entry.safety != Safety::Unsafe
            || entry.value.is_none()
        {
            return Err(ResourceError::Invariant);
        }
        Ok(PreparedCommit {
            environment: self,
            natural: natural::Certificate::default(),
        })
    }
}
