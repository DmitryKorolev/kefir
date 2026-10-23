//! Exact public-export matching after independent restoration and rechecking.
//! This preparation yields request indices only, not permission to publish.
use super::*;
impl Queue {
    pub(super) fn match_export(
        &self,
        request: &Request<'_>,
        order: &Order,
        derived: &mut recursors::Derived,
        parameters: &[NameId],
        work: &mut Working<'_>,
    ) -> Result<(), Stop> {
        let first = request
            .types
            .get(*order.families.first().ok_or(ResourceError::Invariant)? as usize)
            .ok_or(ResourceError::Invariant)?;
        let all = list(request.names, first.all)?;
        let motives = u32::try_from(derived.types.len()).map_err(|_| ResourceError::Counter)?;
        let minors = u32::try_from(derived.rules.len()).map_err(|_| ResourceError::Counter)?;
        let nested = u32::try_from(self.families.len()).map_err(|_| ResourceError::Counter)?;
        if request.recursors.len() != derived.types.len() || !derived.exported.is_empty() {
            return Err(Stop::Unsupported);
        }
        for (member, &index) in order.families.iter().enumerate() {
            let family = &request.types[index as usize];
            let expected = derived.types.get(member).ok_or(ResourceError::Invariant)?;
            if family.num_params != first.num_params
                || family.num_nested != nested
                || family.num_indices != expected.indices
                || family.is_recursive != derived.recursive
                || family.is_reflexive != derived.reflexive
            {
                return Err(Stop::Unsupported);
            }
        }
        for (offset, &index) in order.constructors.iter().enumerate() {
            let expected = derived.rules.get(offset).ok_or(ResourceError::Invariant)?;
            let constructor = &request.constructors[index as usize];
            if constructor.num_fields != expected.fields
                || !same(
                    work.names,
                    constructor.name,
                    expected.constructor,
                    work.budget,
                )?
            {
                return Err(Stop::Unsupported);
            }
        }
        let mut offset = 0usize;
        for expected in &derived.types {
            let mut found = None;
            for (index, exported) in request.recursors.iter().enumerate() {
                if same(work.names, expected.name, exported.name, work.budget)?
                    && found.replace(index).is_some()
                {
                    return Err(Stop::Unsupported);
                }
            }
            let index = found.ok_or(Stop::Unsupported)?;
            let exported = &request.recursors[index];
            if exported.num_params != first.num_params
                || exported.num_indices != expected.indices
                || exported.num_motives != motives
                || exported.num_minors != minors
                || exported.k
                || exported.is_unsafe
                || exported.rules.len != expected.rules
                || !parameters_equal(
                    work.names,
                    parameters,
                    list(request.names, exported.parameters)?,
                    work.budget,
                )?
                || !parameters_equal(
                    work.names,
                    all,
                    list(request.names, exported.all)?,
                    work.budget,
                )?
                || !scheme::matches(work, expected.ty, exported.ty)?
            {
                return Err(Stop::Unsupported);
            }
            let end = offset
                .checked_add(expected.rules as usize)
                .ok_or(ResourceError::Counter)?;
            let rules = derived
                .rules
                .get(offset..end)
                .ok_or(ResourceError::Invariant)?;
            let start = exported.rules.start as usize;
            let limit = start
                .checked_add(exported.rules.len as usize)
                .ok_or(ResourceError::Counter)?;
            let actual = request
                .rules
                .get(start..limit)
                .ok_or(ResourceError::Invariant)?;
            for (expected, actual) in rules.iter().zip(actual) {
                if !same(
                    work.names,
                    expected.constructor,
                    actual.constructor,
                    work.budget,
                )? {
                    return Err(Stop::Unsupported);
                }
                // The restored rule retains the checked expanded telescope's
                // field count. Only the same constructor supplies a negative
                // witness; a reordered/unmatched rule remains inconclusive.
                if expected.fields != actual.num_fields {
                    return Err(Stop::Judgment(Negative::TypeMismatch));
                }
                if !scheme::matches(work, expected.rhs, actual.rhs)? {
                    return Err(Stop::Unsupported);
                }
            }
            push(
                &mut derived.exported,
                u32::try_from(index).map_err(|_| ResourceError::Counter)?,
                work.budget,
            )?;
            offset = end;
        }
        if offset != derived.rules.len() || offset != request.rules.len() {
            return Err(Stop::Unsupported);
        }
        Ok(())
    }
}
