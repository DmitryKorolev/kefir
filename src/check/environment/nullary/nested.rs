//! Storage endpoint for an independently checked and exactly restored nested block.
//! The validator supplies imported roots only. This endpoint checks associations,
//! never establishes positivity, restoration or computation-rule correctness.
use super::*;

pub(in super::super) struct RestoredMetadata<'a> {
    pub family: NameId,
    pub recursor: NameId,
    pub num_indices: u32,
    pub constructor_params: u32,
    pub nonrecursive: bool,
    pub rules: &'a [NullaryRule],
}

impl Environment {
    pub(in super::super) fn prepare_nested_commit(
        &mut self,
        phase: Formation,
        originals: usize,
        metadata: &[RestoredMetadata<'_>],
        names: &Names,
        b: &mut Budget,
    ) -> Result<PreparedCommit<'_>, ResourceError> {
        self.check_visibility(phase.before(), Some(phase))?;
        self.require_public_stage()?;
        let old = self.stage.ok_or(ResourceError::Invariant)?;
        let next = self.next_phase(self.entries.len())?;
        self.stage = Some(Stage { phase: next, ..old });
        if originals == 0 || originals >= metadata.len() {
            return Err(ResourceError::Invariant);
        }
        let count = metadata.iter().try_fold(0usize, |n, m| {
            n.checked_add(m.rules.len()).ok_or(ResourceError::Counter)
        })?;
        let constructors = metadata[..originals].iter().try_fold(0usize, |n, m| {
            n.checked_add(m.rules.len()).ok_or(ResourceError::Counter)
        })?;
        b.charge_work(
            (metadata.len() as u64)
                .checked_mul(8)
                .and_then(|n| n.checked_add((count as u64).checked_mul(4)?))
                .ok_or(ResourceError::Counter)?,
        )?;
        let family_start = self.len();
        let constructor_start = family_start
            .checked_add(originals)
            .ok_or(ResourceError::Counter)?;
        let recursor_start = constructor_start
            .checked_add(constructors)
            .ok_or(ResourceError::Counter)?;
        if self.entries.len()
            != recursor_start
                .checked_add(metadata.len())
                .ok_or(ResourceError::Counter)?
        {
            return Err(ResourceError::Invariant);
        }
        // Original recursors share the checked current block parameter count;
        // extra restored recursors retain their prior constructor count instead.
        let num_params = metadata
            .first()
            .ok_or(ResourceError::Invariant)?
            .constructor_params;
        let common_prefix = u32::try_from(
            metadata
                .len()
                .checked_add(count)
                .ok_or(ResourceError::Counter)?,
        )
        .map_err(|_| ResourceError::Counter)?
        .checked_add(num_params)
        .ok_or(ResourceError::Counter)?;
        let shared_parameters = view(&self.names, self.entries[family_start].parameters)?;
        let rec_parameters = view(&self.names, self.entries[recursor_start].parameters)?;
        let extra = rec_parameters
            .len()
            .checked_sub(shared_parameters.len())
            .ok_or(ResourceError::Invariant)?;
        if extra > 1 {
            return Err(ResourceError::Invariant);
        }
        same_parameters(shared_parameters, &rec_parameters[extra..], names, b)?;
        if extra == 1 {
            let fresh = names.summary(rec_parameters[0], b)?.canonical;
            for &parameter in shared_parameters {
                if names.summary(parameter, b)?.canonical == fresh {
                    return Err(ResourceError::Invariant);
                }
            }
        }
        if self
            .recursors
            .last()
            .is_some_and(|r| r.slot as usize >= recursor_start)
            || self
                .constructors
                .last()
                .is_some_and(|r| r.slot as usize >= constructor_start)
            || self
                .families
                .last()
                .is_some_and(|r| r.slot as usize >= family_start)
        {
            return Err(ResourceError::Invariant);
        }
        let mut constructor_offset = 0usize;
        for (member, m) in metadata.iter().enumerate() {
            if self.staged_slot(m.recursor, SignatureKind::Recursor, names, b)? as usize
                != recursor_start + member
            {
                return Err(ResourceError::Invariant);
            }
            same_parameters(
                rec_parameters,
                view(
                    &self.names,
                    self.entries[recursor_start + member].parameters,
                )?,
                names,
                b,
            )?;
            if member < originals {
                if self.staged_slot(m.family, SignatureKind::Inductive, names, b)? as usize
                    != family_start + member
                    || m.constructor_params != num_params
                {
                    return Err(ResourceError::Invariant);
                }
                same_parameters(
                    shared_parameters,
                    view(&self.names, self.entries[family_start + member].parameters)?,
                    names,
                    b,
                )?;
                for (index, rule) in m.rules.iter().enumerate() {
                    let slot =
                        self.staged_slot(rule.constructor, SignatureKind::Constructor, names, b)?
                            as usize;
                    if slot != constructor_start + constructor_offset + index {
                        return Err(ResourceError::Invariant);
                    }
                    same_parameters(
                        shared_parameters,
                        view(&self.names, self.entries[slot].parameters)?,
                        names,
                        b,
                    )?;
                }
                constructor_offset += m.rules.len();
            } else {
                // Extra recursors reuse prior constructor associations; they may
                // neither introduce a fake prior family nor replace its primary.
                let prior = self
                    .inductive(m.family, family_start, names, b)?
                    .ok_or(ResourceError::Invariant)?;
                if prior.num_params != m.constructor_params
                    || prior.num_indices != m.num_indices
                    || prior.constructors.len() != m.rules.len()
                {
                    return Err(ResourceError::Invariant);
                }
                for (known, rule) in prior.constructors.iter().zip(m.rules) {
                    if names.summary(known.constructor, b)?.canonical
                        != names.summary(rule.constructor, b)?.canonical
                        || known.num_fields != rule.num_fields
                    {
                        return Err(ResourceError::Invariant);
                    }
                }
            }
            if m.rules
                .iter()
                .any(|rule| rule.rhs.slot() >= old.expression_end)
            {
                return Err(ResourceError::Invariant);
            }
        }
        let constructor_end = self
            .constructors
            .len()
            .checked_add(constructors)
            .ok_or(ResourceError::Counter)?;
        let family_end = self
            .families
            .len()
            .checked_add(originals)
            .ok_or(ResourceError::Counter)?;
        let recursor_end = self
            .recursors
            .len()
            .checked_add(metadata.len())
            .ok_or(ResourceError::Counter)?;
        let rule_end = self
            .rules
            .len()
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        span(self.rules.len(), count)?;
        u32::try_from(self.entries.len()).map_err(|_| ResourceError::Counter)?;
        u32::try_from(recursor_end).map_err(|_| ResourceError::Counter)?;
        b.grow_vec(&mut self.constructors, constructor_end)?;
        b.grow_vec(&mut self.families, family_end)?;
        b.grow_vec(&mut self.recursors, recursor_end)?;
        b.grow_vec(&mut self.rules, rule_end)?;
        // All fallible work precedes these invisible logical appends. Only the
        // returned linear PreparedCommit can make the complete suffix visible.
        constructor_offset = 0;
        for (member, m) in metadata.iter().enumerate() {
            let primary = self.recursors.len() as u32;
            if member < originals {
                for index in 0..m.rules.len() {
                    self.constructors.push(ConstructorRecord {
                        slot: (constructor_start + constructor_offset + index) as u32,
                        family: m.family,
                        index: index as u32,
                    });
                }
                self.families.push(FamilyRecord {
                    slot: (family_start + member) as u32,
                    primary,
                });
                constructor_offset += m.rules.len();
            }
            let rules = Span {
                offset: self.rules.len() as u32,
                len: m.rules.len() as u32,
            };
            self.rules.extend_from_slice(m.rules);
            self.recursors.push(RecursorRecord {
                slot: (recursor_start + member) as u32,
                family: m.family,
                rules,
                k: false,
                nonrecursive: m.nonrecursive,
                num_params,
                num_indices: m.num_indices,
                common_prefix,
                constructor_params: m.constructor_params,
            });
        }
        Ok(PreparedCommit {
            environment: self,
            natural: natural::Certificate::default(),
        })
    }
}
