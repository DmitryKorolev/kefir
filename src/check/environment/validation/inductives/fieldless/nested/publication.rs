//! Request-local checked associations. No generated syntax handle is retained.
use super::*;
use crate::check::environment::PreparedCommit;
use crate::check::environment::nullary::RestoredMetadata;

#[derive(Clone, Copy)]
pub(super) struct Recursor {
    pub exported: u32,
    pub family: NameId,
    pub indices: u32,
    pub constructor_params: u32,
}
const _: () = assert!(size_of::<Recursor>() == 16);
#[derive(Default)]
pub(super) struct Publication {
    pub families: Vec<u32>,
    pub constructors: Vec<u32>,
    pub recursors: Vec<Recursor>,
    pub before: usize,
    pub recursive: bool,
    pub ready: bool,
}
impl Publication {
    pub(super) fn prepare<'a>(
        &self,
        request: &Request<'_>,
        environment: &'a mut Environment,
        decoder: &Decoder,
        budget: &mut Budget,
    ) -> Result<PreparedCommit<'a>, ResourceError> {
        if !self.ready || environment.len() != self.before {
            return Err(ResourceError::Invariant);
        }
        let names = decoder.syntax().0;
        let expressions = decoder.syntax().2.len();
        let levels = decoder.syntax().1.len();
        let first = request
            .types
            .get(*self.families.first().ok_or(ResourceError::Invariant)? as usize)
            .ok_or(ResourceError::Invariant)?;
        let parameters = list(request.names, first.parameters)?;
        let all = list(request.names, first.all)?;
        let mut phase = environment.begin_stage(expressions, levels, budget)?;
        for &index in &self.families {
            let family = &request.types[index as usize];
            phase = environment.stage_signature(
                phase,
                SignatureInput {
                    kind: SignatureKind::Inductive,
                    name: family.name,
                    parameters,
                    ty: family.ty,
                    all,
                },
                names,
                budget,
            )?;
        }
        for &index in &self.constructors {
            let constructor = &request.constructors[index as usize];
            phase = environment.stage_signature(
                phase,
                SignatureInput {
                    kind: SignatureKind::Constructor,
                    name: constructor.name,
                    parameters,
                    ty: constructor.ty,
                    all,
                },
                names,
                budget,
            )?;
        }
        for row in &self.recursors {
            let recursor = &request.recursors[row.exported as usize];
            phase = environment.stage_signature(
                phase,
                SignatureInput {
                    kind: SignatureKind::Recursor,
                    name: recursor.name,
                    parameters: list(request.names, recursor.parameters)?,
                    ty: recursor.ty,
                    all,
                },
                names,
                budget,
            )?;
        }
        let mut rules = Vec::new();
        let mut metadata = Vec::new();
        let filled = (|| {
            budget.grow_vec(&mut rules, request.rules.len())?;
            budget.charge_work(request.rules.len() as u64)?;
            for row in &self.recursors {
                let recursor = &request.recursors[row.exported as usize];
                let start = recursor.rules.start as usize;
                let end = start
                    .checked_add(recursor.rules.len as usize)
                    .ok_or(ResourceError::Counter)?;
                for rule in request
                    .rules
                    .get(start..end)
                    .ok_or(ResourceError::Invariant)?
                {
                    rules.push(NullaryRule {
                        constructor: rule.constructor,
                        rhs: rule.rhs,
                        num_fields: rule.num_fields,
                    });
                }
            }
            Ok::<(), ResourceError>(())
        })();
        let rule_slice = rules.as_slice();
        let filled = filled.and_then(|()| {
            budget.grow_vec(&mut metadata, self.recursors.len())?;
            let mut offset = 0usize;
            for row in &self.recursors {
                let recursor = &request.recursors[row.exported as usize];
                let end = offset
                    .checked_add(recursor.rules.len as usize)
                    .ok_or(ResourceError::Counter)?;
                metadata.push(RestoredMetadata {
                    family: row.family,
                    recursor: recursor.name,
                    num_indices: row.indices,
                    constructor_params: row.constructor_params,
                    nonrecursive: !self.recursive,
                    rules: rule_slice
                        .get(offset..end)
                        .ok_or(ResourceError::Invariant)?,
                });
                offset = end;
            }
            Ok::<(), ResourceError>(())
        });
        let prepared = match filled {
            Ok(()) => environment.prepare_nested_commit(
                phase,
                self.families.len(),
                &metadata,
                names,
                budget,
            ),
            Err(error) => Err(error),
        };
        // Before publishing, all temporary owners and every fallible cleanup
        // complete. A failed cleanup drops the still-private linear token.
        let metadata_bytes = metadata
            .capacity()
            .checked_mul(size_of::<RestoredMetadata<'_>>())
            .ok_or(ResourceError::Counter)?;
        drop(metadata);
        let rules_bytes = rules
            .capacity()
            .checked_mul(size_of::<NullaryRule>())
            .ok_or(ResourceError::Counter)?;
        drop(rules);
        budget.release(metadata_bytes as u64)?;
        budget.release(rules_bytes as u64)?;
        prepared
    }
    pub(super) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        let bytes = (self.families.capacity() + self.constructors.capacity())
            .checked_mul(4)
            .and_then(|n| {
                n.checked_add(
                    self.recursors
                        .capacity()
                        .checked_mul(size_of::<Recursor>())?,
                )
            })
            .ok_or(ResourceError::Counter)?;
        drop(self);
        budget.release(bytes as u64)
    }
}
