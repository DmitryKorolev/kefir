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

/// Named view of one generated `DECLARATIONS` row. Sequence fields name
/// `SEQUENCES` rows; `schema.rs` checks every field's range at compile time.
#[derive(Clone, Copy)]
struct Declaration {
    name: u32,
    kind: u32,
    parameters: u32,
    ty: u32,
    /// Zero for every group member: families, constructors and recursors have
    /// no value.
    value: u32,
    /// Family and recursor `all`; empty for a constructor.
    all: u32,
    /// Family constructor names; empty otherwise.
    constructors: u32,
    /// Recursor rules as `[constructor, fields, rhs]` triples; empty otherwise.
    rules: u32,
    /// `[key, value]` pairs in generated order; keys are in [`key`].
    metadata: u32,
    /// Constructor's inductive name; zero otherwise.
    inductive: u32,
    dependencies: u32,
    group: u32,
}
impl From<&[u32; 12]> for Declaration {
    fn from(row: &[u32; 12]) -> Self {
        let [
            name,
            kind,
            parameters,
            ty,
            value,
            all,
            constructors,
            rules,
            metadata,
            inductive,
            dependencies,
            group,
        ] = *row;
        Self {
            name,
            kind,
            parameters,
            ty,
            value,
            all,
            constructors,
            rules,
            metadata,
            inductive,
            dependencies,
            group,
        }
    }
}

/// Metadata keys shared by every declaration kind in the manifest.
mod key {
    pub(super) const UNSAFE: u32 = 1;
    pub(super) const RECURSIVE: u32 = 2;
    pub(super) const REFLEXIVE: u32 = 3;
    pub(super) const K: u32 = 4;
    pub(super) const PARAMETERS: u32 = 5;
    pub(super) const INDICES: u32 = 6;
    pub(super) const NESTED: u32 = 7;
    pub(super) const FIELDS: u32 = 8;
    pub(super) const CONSTRUCTOR_INDEX: u32 = 9;
    pub(super) const MOTIVES: u32 = 10;
    pub(super) const MINORS: u32 = 11;
}

/// Exactly these pairs, in this order.
fn metadata(sequence: u32, expected: &[(u32, u32)]) -> Result<bool, ResourceError> {
    let (pairs, rest) = matching::sequence(sequence)?.as_chunks::<2>();
    Ok(rest.is_empty()
        && pairs.len() == expected.len()
        && pairs
            .iter()
            .zip(expected)
            .all(|(&[k, v], &(ek, ev))| k == ek && v == ev))
}

fn empty(sequence: u32) -> Result<bool, ResourceError> {
    Ok(matching::sequence(sequence)?.is_empty())
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
        row: Declaration,
        request: &Group<'_>,
        n: &Names,
        l: &Levels,
        e: &Expressions,
        b: &mut Budget,
    ) -> Result<bool, ResourceError> {
        if row.kind != self.kind() || row.value != 0 {
            return Err(ResourceError::Invariant);
        }
        if !names(
            row.parameters,
            list(request.names, self.parameters())?,
            n,
            b,
        )? || !matching::expression(row.ty, self.ty(), e, l, n, b)?
        {
            return Ok(false);
        }
        match self {
            Self::Family(x) => {
                if row.inductive != 0 || !empty(row.rules)? {
                    return Err(ResourceError::Invariant);
                }
                Ok(metadata(
                    row.metadata,
                    &[
                        (key::UNSAFE, u32::from(x.is_unsafe)),
                        (key::RECURSIVE, u32::from(x.is_recursive)),
                        (key::REFLEXIVE, u32::from(x.is_reflexive)),
                        (key::PARAMETERS, x.num_params),
                        (key::INDICES, x.num_indices),
                        (key::NESTED, x.num_nested),
                    ],
                )? && names(row.all, list(request.names, x.all)?, n, b)?
                    && names(row.constructors, list(request.names, x.constructors)?, n, b)?)
            }
            Self::Constructor(x) => {
                if !empty(row.all)? || !empty(row.constructors)? || !empty(row.rules)? {
                    return Err(ResourceError::Invariant);
                }
                Ok(metadata(
                    row.metadata,
                    &[
                        (key::UNSAFE, u32::from(x.is_unsafe)),
                        (key::PARAMETERS, x.num_params),
                        (key::FIELDS, x.num_fields),
                        (key::CONSTRUCTOR_INDEX, x.index),
                    ],
                )? && matching::name(row.inductive, x.inductive, n, b)?)
            }
            Self::Recursor(x) => {
                if row.inductive != 0 || !empty(row.constructors)? {
                    return Err(ResourceError::Invariant);
                }
                if !metadata(
                    row.metadata,
                    &[
                        (key::UNSAFE, u32::from(x.is_unsafe)),
                        (key::K, u32::from(x.k)),
                        (key::PARAMETERS, x.num_params),
                        (key::INDICES, x.num_indices),
                        (key::MOTIVES, x.num_motives),
                        (key::MINORS, x.num_minors),
                    ],
                )? || !names(row.all, list(request.names, x.all)?, n, b)?
                {
                    return Ok(false);
                }
                let rules = list(request.rules, x.rules)?;
                let (expected, rest) = matching::sequence(row.rules)?.as_chunks::<3>();
                if !rest.is_empty() {
                    return Err(ResourceError::Invariant);
                }
                if expected.len() != rules.len() {
                    return Ok(false);
                }
                b.charge_work(rules.len() as u64 + 1)?;
                for (&[constructor, fields, rhs], actual) in expected.iter().zip(rules) {
                    if fields != actual.num_fields
                        || !matching::name(constructor, actual.constructor, n, b)?
                        || !matching::expression(rhs, actual.rhs, e, l, n, b)?
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
    pub(in super::super) fn prepare_finite_group(
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
                        let row = Declaration::from(row);
                        if row.name != expected_name
                            || row.kind != member.kind()
                            || row.group != group_id
                            || manifest::ALTERNATIVE_PIN_MASKS[index] & (1 << pin) == 0
                            || !previous.dependencies(pin, row.dependencies, &internal)?
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
