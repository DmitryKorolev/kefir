//! Complete original group alternatives only. Internal dependencies are allowed
//! while matching, but no member bit is retained until every member matches the
//! same pin. Returned evidence is inert until the validator atomically publishes.
use super::*;
use crate::decode::primitive_decode::inductives::{
    Constructor, Inductive, Recursor, Request as Group, Span,
};

fn list<T>(values: &[T], span: Span) -> Result<&[T], ResourceError> {
    let end = (span.start as usize)
        .checked_add(span.len as usize)
        .ok_or(ResourceError::Counter)?;
    values
        .get(span.start as usize..end)
        .ok_or(ResourceError::Invariant)
}

fn ordered_names(
    sequence: u32,
    actual: impl ExactSizeIterator<Item = NameId>,
    n: &Names,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    let expected = matching::sequence(sequence)?;
    if expected.len() != actual.len() {
        return Ok(false);
    }
    b.charge_work(expected.len() as u64 + 1)?;
    for (&expected, actual) in expected.iter().zip(actual) {
        if !matching::name(expected, actual, n, b)? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[derive(Clone, Copy)]
enum Member<'a> {
    Family(&'a Inductive),
    Constructor(&'a Constructor),
    Recursor(&'a Recursor),
}
impl Member<'_> {
    fn name(self) -> NameId {
        match self {
            Self::Family(x) => x.name,
            Self::Constructor(x) => x.name,
            Self::Recursor(x) => x.name,
        }
    }
    fn ty(self) -> ExprId {
        match self {
            Self::Family(x) => x.ty,
            Self::Constructor(x) => x.ty,
            Self::Recursor(x) => x.ty,
        }
    }
    fn kind(self) -> u32 {
        match self {
            Self::Family(_) => 0,
            Self::Constructor(_) => 1,
            Self::Recursor(_) => 2,
        }
    }
    fn signature_kind(self) -> SignatureKind {
        match self {
            Self::Family(_) => SignatureKind::Inductive,
            Self::Constructor(_) => SignatureKind::Constructor,
            Self::Recursor(_) => SignatureKind::Recursor,
        }
    }
    fn parameters(self) -> Span {
        match self {
            Self::Family(x) => x.parameters,
            Self::Constructor(x) => x.parameters,
            Self::Recursor(x) => x.parameters,
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn matches(
        self,
        row: &[u32; 12],
        request: &Group<'_>,
        n: &Names,
        l: &Levels,
        e: &Expressions,
        b: &mut Budget,
    ) -> Result<bool, ResourceError> {
        if row[1] != self.kind() || row[4] != 0 {
            return Err(ResourceError::Invariant);
        }
        if !names(row[2], list(request.names, self.parameters())?, n, b)?
            || !matching::expression(row[3], self.ty(), e, l, n, b)?
        {
            return Ok(false);
        }
        let metadata = matching::sequence(row[8])?;
        match self {
            Self::Family(x) => {
                if row[9] != 0 || !matching::sequence(row[7])?.is_empty() {
                    return Err(ResourceError::Invariant);
                }
                Ok(metadata
                    == [
                        1,
                        u32::from(x.is_unsafe),
                        2,
                        u32::from(x.is_recursive),
                        3,
                        u32::from(x.is_reflexive),
                        5,
                        x.num_params,
                        6,
                        x.num_indices,
                        7,
                        x.num_nested,
                    ]
                    && names(row[5], list(request.names, x.all)?, n, b)?
                    && names(row[6], list(request.names, x.constructors)?, n, b)?)
            }
            Self::Constructor(x) => {
                if !matching::sequence(row[5])?.is_empty()
                    || !matching::sequence(row[6])?.is_empty()
                    || !matching::sequence(row[7])?.is_empty()
                {
                    return Err(ResourceError::Invariant);
                }
                Ok(metadata
                    == [
                        1,
                        u32::from(x.is_unsafe),
                        5,
                        x.num_params,
                        8,
                        x.num_fields,
                        9,
                        x.index,
                    ]
                    && matching::name(row[9], x.inductive, n, b)?)
            }
            Self::Recursor(x) => {
                if row[9] != 0 || !matching::sequence(row[6])?.is_empty() {
                    return Err(ResourceError::Invariant);
                }
                if metadata
                    != [
                        1,
                        u32::from(x.is_unsafe),
                        4,
                        u32::from(x.k),
                        5,
                        x.num_params,
                        6,
                        x.num_indices,
                        10,
                        x.num_motives,
                        11,
                        x.num_minors,
                    ]
                    || !names(row[5], list(request.names, x.all)?, n, b)?
                {
                    return Ok(false);
                }
                let rules = list(request.rules, x.rules)?;
                let expected = matching::sequence(row[7])?;
                if expected.len() % 3 != 0 {
                    return Err(ResourceError::Invariant);
                }
                if expected.len() / 3 != rules.len() {
                    return Ok(false);
                }
                b.charge_work(rules.len() as u64 + 1)?;
                for (expected, actual) in expected.as_chunks::<3>().0.iter().zip(rules) {
                    if expected[1] != actual.num_fields
                        || !matching::name(expected[0], actual.constructor, n, b)?
                        || !matching::expression(expected[2], actual.rhs, e, l, n, b)?
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    }
}
fn members<'a>(request: &'a Group<'_>) -> impl Iterator<Item = Member<'a>> + Clone {
    request
        .types
        .iter()
        .map(Member::Family)
        .chain(request.constructors.iter().map(Member::Constructor))
        .chain(request.recursors.iter().map(Member::Recursor))
}
impl Environment {
    /// The caller has completed ordinary original group validation and all
    /// session cleanup. This copy is not committed authority. Auxiliary stages
    /// cannot call this endpoint; its original signatures must still be live.
    #[allow(clippy::too_many_arguments)]
    pub(in super::super) fn prepare_getbang_group(
        &self,
        previous: Certificate,
        request: &Group<'_>,
        n: &Names,
        l: &Levels,
        e: &Expressions,
        b: &mut Budget,
    ) -> Result<Certificate, ResourceError> {
        self.require_public_stage()?;
        if previous.frontier != 0 {
            return Ok(previous);
        }
        let Some(first) = request.types.first() else {
            return Err(ResourceError::Invariant);
        };
        let Some(first_ref) = candidate(first.name, n, b)? else {
            return Ok(previous);
        };
        let first_name = manifest::REFERENT_NAMES[first_ref];
        let phase = self.stage.ok_or(ResourceError::Invariant)?.phase;
        self.check_visibility(phase.before(), Some(phase))?;
        let total = request
            .types
            .len()
            .checked_add(request.constructors.len())
            .and_then(|x| x.checked_add(request.recursors.len()))
            .ok_or(ResourceError::Counter)?;
        if self.entries.len().checked_sub(self.len()) != Some(total) {
            return Err(ResourceError::Invariant);
        }
        let after = u32::try_from(self.entries.len()).map_err(|_| ResourceError::Counter)?;
        let mut next = previous;
        b.charge_work(manifest::GROUPS.len() as u64 + 1)?;
        for (group_index, &[families, constructors, recursors]) in
            manifest::GROUPS.iter().enumerate()
        {
            if matching::sequence(families)?.first().copied() != Some(first_name) {
                continue;
            }
            if !ordered_names(families, request.types.iter().map(|x| x.name), n, b)?
                || !ordered_names(
                    constructors,
                    request.constructors.iter().map(|x| x.name),
                    n,
                    b,
                )?
                || !ordered_names(recursors, request.recursors.iter().map(|x| x.name), n, b)?
            {
                continue;
            }
            let group_id = u32::try_from(group_index + 1).map_err(|_| ResourceError::Counter)?;
            let mut internal = [0u32; manifest::MASK_WORDS];
            for member in members(request) {
                let referent = candidate(member.name(), n, b)?.ok_or(ResourceError::Invariant)?;
                let bit = 1 << (referent % 32);
                if internal[referent / 32] & bit != 0 {
                    return Err(ResourceError::Invariant);
                }
                internal[referent / 32] |= bit;
            }
            for pin in 0..2 {
                let mut complete = true;
                for member in members(request) {
                    let referent =
                        candidate(member.name(), n, b)?.ok_or(ResourceError::Invariant)?;
                    let expected_name = manifest::REFERENT_NAMES[referent];
                    let mut matched = false;
                    b.charge_work(
                        manifest::DECLARATIONS.len() as u64 + manifest::MASK_WORDS as u64,
                    )?;
                    for (index, row) in manifest::DECLARATIONS.iter().enumerate() {
                        if row[0] != expected_name
                            || row[1] != member.kind()
                            || row[11] != group_id
                            || manifest::ALTERNATIVE_PIN_MASKS[index] & (1 << pin) == 0
                            || !previous.dependencies(pin, row[10], &internal)?
                        {
                            continue;
                        }
                        if member.matches(row, request, n, l, e, b)? {
                            matched = true;
                            break;
                        }
                    }
                    if !matched {
                        complete = false;
                        break;
                    }
                }
                if !complete {
                    continue;
                }
                // Exact staged slots, not input-array offsets: mutual validation
                // may stage constructors/recursors in derived ownership order.
                // No staged row contributes authority before the whole pin matches.
                for member in members(request) {
                    let referent =
                        candidate(member.name(), n, b)?.ok_or(ResourceError::Invariant)?;
                    let signature = self
                        .lookup_visible(member.name(), phase.before(), Some(phase), n, b)?
                        .ok_or(ResourceError::Invariant)?;
                    let slot = signature.slot.ok_or(ResourceError::Invariant)?;
                    if slot < self.committed
                        || signature.kind != StoredKind::Signature(member.signature_kind())
                        || signature.ty != TypeSource::Original(member.ty())
                    {
                        return Err(ResourceError::Invariant);
                    }
                    next.insert(
                        pin,
                        referent,
                        slot.checked_add(1).ok_or(ResourceError::Counter)?,
                    )?;
                }
            }
        }
        next.finish(after)?;
        Ok(next)
    }
}
