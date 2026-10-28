//! Committed computation metadata, with explicit primary-family associations.
//! Exact formation/RHS matching and K eligibility remain validator obligations.
use super::*;
mod nested;
pub(super) use nested::RestoredMetadata;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct NullaryRule {
    pub constructor: NameId,
    pub rhs: ExprId,
    pub num_fields: u32,
}
pub(crate) struct NullaryMetadata<'a> {
    pub family: NameId,
    pub recursor: NameId,
    pub k: bool,
    /// Derived by the checked constructor pass, never copied from export metadata.
    pub nonrecursive: bool,
    /// Derived term-telescope counts, supplied only after exact signature/RHS checks.
    pub num_params: u32,
    pub num_indices: u32,
    pub rules: &'a [NullaryRule],
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ConstructorView {
    pub name: NameId,
    pub family: NameId,
    pub index: u32,
}
pub(crate) struct RecursorView<'a> {
    pub family: NameId,
    pub k: bool,
    /// Block parameters, all motives and all minors, excluding indices/major.
    pub common_prefix: u32,
    /// Parameters of the target constructor, which may differ for restored helpers.
    pub constructor_params: u32,
    pub num_indices: u32,
    pub rules: &'a [NullaryRule],
}
/// Borrowed committed family metadata; no additional retained field plan.
pub(crate) struct InductiveView<'a> {
    pub nonrecursive: bool,
    pub num_params: u32,
    pub num_indices: u32,
    pub constructors: &'a [NullaryRule],
}
const _: () = assert!(size_of::<RecursorView<'_>>() == 40);
const _: () = assert!(size_of::<InductiveView<'_>>() == 32);

#[derive(Clone, Copy)]
pub(super) struct ConstructorRecord {
    slot: u32,
    family: NameId,
    index: u32,
}
#[derive(Clone, Copy)]
pub(super) struct FamilyRecord {
    slot: u32,
    primary: u32,
}
const _: () = assert!(size_of::<FamilyRecord>() == 8);

#[derive(Clone, Copy)]
pub(super) struct RecursorRecord {
    slot: u32,
    family: NameId,
    rules: Span,
    k: bool,
    nonrecursive: bool,
    num_params: u32,
    num_indices: u32,
    common_prefix: u32,
    constructor_params: u32,
}
const _: () = assert!(size_of::<ConstructorRecord>() == 12);
const _: () = assert!(size_of::<RecursorRecord>() == 36);
const _: () = assert!(size_of::<NullaryRule>() == 12);

fn same_parameters(
    left: &[NameId],
    right: &[NameId],
    names: &Names,
    b: &mut Budget,
) -> Result<(), ResourceError> {
    if left.len() != right.len() {
        return Err(ResourceError::Invariant);
    }
    b.charge_work(left.len() as u64 + 1)?;
    for (&a, &z) in left.iter().zip(right) {
        if names.summary(a, b)?.canonical != names.summary(z, b)?.canonical {
            return Err(ResourceError::Invariant);
        }
    }
    Ok(())
}

impl Environment {
    fn staged_slot(
        &self,
        name: NameId,
        kind: SignatureKind,
        names: &Names,
        b: &mut Budget,
    ) -> Result<u32, ResourceError> {
        let key = names.summary(name, b)?.canonical as usize;
        let encoded = self
            .by_name
            .get(key)
            .copied()
            .ok_or(ResourceError::Invariant)?;
        let slot = encoded.checked_sub(1).ok_or(ResourceError::Invariant)?;
        let entry = self
            .entries
            .get(slot as usize)
            .ok_or(ResourceError::Invariant)?;
        if slot < self.committed
            || entry.kind != StoredKind::Signature(kind)
            || entry.value.is_some()
            || entry.safety != Safety::Safe
        {
            return Err(ResourceError::Invariant);
        }
        Ok(slot)
    }
    /// After all generated checking state has retired, prepare the exact original
    /// RHS roots and derived metadata for one family. Scope here is deliberately
    /// one nonrecursive family, not a general inductive transaction framework.
    /// Caller derives term parameter/index counts and K, checks all
    /// constructor/rule correspondence and type preservation. This method enforces storage association, not those semantics.
    pub(super) fn prepare_nullary_commit(
        &mut self,
        phase: Formation,
        metadata: NullaryMetadata<'_>,
        names: &Names,
        b: &mut Budget,
    ) -> Result<PreparedCommit<'_>, ResourceError> {
        self.prepare_inductive_commit(phase, std::slice::from_ref(&metadata), names, b)
    }

    /// Storage endpoint for an already derived safe non-nested block. The caller
    /// supplies one primary recursor per family, with family-local rules. Staging
    /// order is all families, all constructors in family order, then all recursors.
    /// This checks storage invariants only; it never derives semantic authority.
    pub(super) fn prepare_inductive_commit(
        &mut self,
        phase: Formation,
        metadata: &[NullaryMetadata<'_>],
        names: &Names,
        b: &mut Budget,
    ) -> Result<PreparedCommit<'_>, ResourceError> {
        self.check_visibility(phase.before(), Some(phase))?;
        self.require_public_stage()?;
        let old = self.stage.ok_or(ResourceError::Invariant)?;
        // Invalidate even a failed preparation's old token.
        let next = self.next_phase(self.entries.len())?;
        self.stage = Some(Stage { phase: next, ..old });
        let first = metadata.first().ok_or(ResourceError::Invariant)?;
        let families = metadata.len();
        b.charge_work(
            (families as u64)
                .checked_mul(8)
                .ok_or(ResourceError::Counter)?,
        )?;
        let count = metadata.iter().try_fold(0usize, |sum, m| {
            sum.checked_add(m.rules.len()).ok_or(ResourceError::Counter)
        })?;
        b.charge_work(
            (count as u64)
                .checked_mul(4)
                .ok_or(ResourceError::Counter)?,
        )?;
        let expected = families
            .checked_mul(2)
            .and_then(|n| n.checked_add(count))
            .ok_or(ResourceError::Counter)?;
        if self.entries.len().checked_sub(self.len()) != Some(expected) {
            return Err(ResourceError::Invariant);
        }
        let common_prefix =
            u32::try_from(count.checked_add(families).ok_or(ResourceError::Counter)?)
                .ok()
                .and_then(|n| n.checked_add(first.num_params))
                .ok_or(ResourceError::Counter)?;
        let family_start = self.len();
        let constructor_start = family_start
            .checked_add(families)
            .ok_or(ResourceError::Counter)?;
        let recursor_start = constructor_start
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        u32::try_from(self.entries.len()).map_err(|_| ResourceError::Counter)?;
        if self
            .recursors
            .last()
            .is_some_and(|row| row.slot as usize >= recursor_start)
            || self
                .constructors
                .last()
                .is_some_and(|row| row.slot as usize >= constructor_start)
            || self
                .families
                .last()
                .is_some_and(|row| row.slot as usize >= family_start)
        {
            return Err(ResourceError::Invariant);
        }
        let shared_parameters = view(&self.names, self.entries[family_start].parameters)?;
        let shared_rec_parameters = view(&self.names, self.entries[recursor_start].parameters)?;
        let mut constructor_offset = 0;
        for (member, m) in metadata.iter().enumerate() {
            let family = self.staged_slot(m.family, SignatureKind::Inductive, names, b)?;
            let recursor = self.staged_slot(m.recursor, SignatureKind::Recursor, names, b)?;
            if family as usize != family_start + member
                || recursor as usize != recursor_start + member
                || m.num_params != first.num_params
                || (m.k && (families != 1 || m.rules.len() != 1))
            {
                return Err(ResourceError::Invariant);
            }
            let parameters = view(&self.names, self.entries[family as usize].parameters)?;
            let rec_parameters = view(&self.names, self.entries[recursor as usize].parameters)?;
            if member != 0 {
                same_parameters(shared_parameters, parameters, names, b)?;
                same_parameters(shared_rec_parameters, rec_parameters, names, b)?;
            }
            // Fresh elimination universe may prefix the identical ordered scope.
            let extra = rec_parameters
                .len()
                .checked_sub(parameters.len())
                .ok_or(ResourceError::Invariant)?;
            if extra > 1 {
                return Err(ResourceError::Invariant);
            }
            same_parameters(parameters, &rec_parameters[extra..], names, b)?;
            if extra == 1 {
                b.charge_work(parameters.len() as u64 + 1)?;
                let fresh = names.summary(rec_parameters[0], b)?.canonical;
                for &parameter in parameters {
                    if names.summary(parameter, b)?.canonical == fresh {
                        return Err(ResourceError::Invariant);
                    }
                }
            }
            for (index, rule) in m.rules.iter().enumerate() {
                let slot =
                    self.staged_slot(rule.constructor, SignatureKind::Constructor, names, b)?;
                same_parameters(
                    parameters,
                    view(&self.names, self.entries[slot as usize].parameters)?,
                    names,
                    b,
                )?;
                if slot as usize != constructor_start + constructor_offset + index
                    || rule.rhs.slot() >= old.expression_end
                    || (m.k && rule.num_fields != 0)
                {
                    return Err(ResourceError::Invariant);
                }
            }
            constructor_offset += m.rules.len(); // bounded by checked total count
        }
        let constructor_end = self
            .constructors
            .len()
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        let recursor_end = self
            .recursors
            .len()
            .checked_add(families)
            .ok_or(ResourceError::Counter)?;
        let family_end = self
            .families
            .len()
            .checked_add(families)
            .ok_or(ResourceError::Counter)?;
        let rule_end = self
            .rules
            .len()
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        // Every span and primary index below fits before any logical append.
        span(self.rules.len(), count)?;
        u32::try_from(recursor_end).map_err(|_| ResourceError::Counter)?;
        b.grow_vec(&mut self.constructors, constructor_end)?;
        b.grow_vec(&mut self.recursors, recursor_end)?;
        b.grow_vec(&mut self.rules, rule_end)?;
        b.grow_vec(&mut self.families, family_end)?;
        // No fallible operation follows the first append. These rows remain
        // invisible if PreparedCommit is abandoned instead of publishing once.
        constructor_offset = 0;
        for (member, m) in metadata.iter().enumerate() {
            for index in 0..m.rules.len() {
                self.constructors.push(ConstructorRecord {
                    slot: (constructor_start + constructor_offset + index) as u32,
                    family: m.family,
                    index: index as u32,
                });
            }
            let rules = Span {
                offset: self.rules.len() as u32,
                len: m.rules.len() as u32,
            };
            self.rules.extend_from_slice(m.rules);
            let primary = self.recursors.len() as u32;
            self.recursors.push(RecursorRecord {
                slot: (recursor_start + member) as u32,
                family: m.family,
                rules,
                k: m.k,
                nonrecursive: m.nonrecursive,
                num_params: m.num_params,
                num_indices: m.num_indices,
                common_prefix,
                constructor_params: m.num_params,
            });
            self.families.push(FamilyRecord {
                slot: (family_start + member) as u32,
                primary,
            });
            constructor_offset += m.rules.len();
        }
        Ok(PreparedCommit {
            environment: self,
            natural: natural::Certificate::default(),
        })
    }
    fn computation_slot(
        &self,
        name: NameId,
        before: usize,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Option<u32>, ResourceError> {
        b.observe(Event::EnvironmentLookups, 1);
        b.charge_work(1)?;
        if before > self.len() {
            return Err(ResourceError::Invariant);
        }
        let key = names.summary(name, b)?.canonical as usize;
        let encoded = self.by_name.get(key).copied().unwrap_or(0);
        if encoded == 0 || encoded as usize > before {
            return Ok(None);
        }
        Ok(Some(encoded - 1))
    }
    /// Primary association is fixed at the family's atomic commit. Later helper
    /// recursors cannot replace it. Both rows must be below the caller's frontier;
    /// an abandoned prepared suffix grants no observation authority.
    pub(crate) fn inductive(
        &self,
        name: NameId,
        before: usize,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Option<InductiveView<'_>>, ResourceError> {
        let Some(slot) = self.computation_slot(name, before, names, b)? else {
            return Ok(None);
        };
        if self.entries[slot as usize].kind != StoredKind::Signature(SignatureKind::Inductive) {
            return Ok(None);
        }
        b.charge_work(u64::from(self.families.len().checked_ilog2().unwrap_or(0)) + 2)?;
        let index = self
            .families
            .binary_search_by_key(&slot, |row| row.slot)
            .map_err(|_| ResourceError::Invariant)?;
        let record = self
            .recursors
            .get(self.families[index].primary as usize)
            .ok_or(ResourceError::Invariant)?;
        if record.slot as usize >= before
            || names.summary(record.family, b)?.canonical != names.summary(name, b)?.canonical
        {
            return Err(ResourceError::Invariant);
        }
        Ok(Some(InductiveView {
            nonrecursive: record.nonrecursive,
            num_params: record.num_params,
            num_indices: record.num_indices,
            constructors: view(&self.rules, record.rules)?,
        }))
    }

    /// None supplies no computation permission and no evidence of rigidity.
    /// Recognized recursors without usable metadata remain unsupported when their
    /// reduction is demanded. Formation scopes cannot raise `before` past commit.
    pub(crate) fn recursor(
        &self,
        name: NameId,
        before: usize,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Option<RecursorView<'_>>, ResourceError> {
        let Some(slot) = self.computation_slot(name, before, names, b)? else {
            return Ok(None);
        };
        b.charge_work(u64::from(self.recursors.len().checked_ilog2().unwrap_or(0)) + 2)?;
        let Ok(index) = self
            .recursors
            .binary_search_by_key(&slot, |record| record.slot)
        else {
            return Ok(None);
        };
        let record = &self.recursors[index];
        Ok(Some(RecursorView {
            family: record.family,
            k: record.k,
            common_prefix: record.common_prefix,
            constructor_params: record.constructor_params,
            num_indices: record.num_indices,
            rules: view(&self.rules, record.rules)?,
        }))
    }
    /// Constructor identity is exact structured-name lookup, not display text.
    pub(crate) fn constructor(
        &self,
        name: NameId,
        before: usize,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Option<ConstructorView>, ResourceError> {
        let Some(slot) = self.computation_slot(name, before, names, b)? else {
            return Ok(None);
        };
        b.charge_work(u64::from(self.constructors.len().checked_ilog2().unwrap_or(0)) + 2)?;
        let Ok(index) = self
            .constructors
            .binary_search_by_key(&slot, |record| record.slot)
        else {
            return Ok(None);
        };
        let record = &self.constructors[index];
        let entry = self
            .entries
            .get(slot as usize)
            .ok_or(ResourceError::Invariant)?;
        Ok(Some(ConstructorView {
            name: entry.name,
            family: record.family,
            index: record.index,
        }))
    }
    /// Called by the State owner also after failed/abandoned staging. No metadata
    /// row must be visited to reclaim its flat capacities.
    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let capacities = [
            (self.entries.capacity(), size_of::<Template>()),
            (self.by_name.capacity(), size_of::<u32>()),
            (self.names.capacity(), size_of::<NameId>()),
            (self.hints.capacity(), 1),
            (self.constructors.capacity(), size_of::<ConstructorRecord>()),
            (self.recursors.capacity(), size_of::<RecursorRecord>()),
            (self.families.capacity(), size_of::<FamilyRecord>()),
            (self.rules.capacity(), size_of::<NullaryRule>()),
            (self.no_rule.capacity(), size_of::<u64>()),
        ];
        let bytes = capacities
            .into_iter()
            .try_fold(0usize, |sum, (count, width)| {
                count
                    .checked_mul(width)
                    .and_then(|n| sum.checked_add(n))
                    .ok_or(ResourceError::Counter)
            })?;
        drop(self);
        b.release(bytes as u64)
    }
}
