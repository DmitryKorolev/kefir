//! Restoration produces checked public syntax, not an admission certificate.
//! Private locals have already retired; no checkedness from a context containing
//! helper types is reused while the restored roots are independently inferred.
use super::*;

impl Queue {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn restore_and_recheck(
        &self,
        request: &Request<'_>,
        order: &Order,
        derived: &mut recursors::Derived,
        work: &mut Working<'_>,
        environment: &mut Environment,
        ends: (usize, usize),
    ) -> Result<(), Stop> {
        let first = request
            .types
            .get(*order.families.first().ok_or(ResourceError::Invariant)? as usize)
            .ok_or(ResourceError::Invariant)?;
        let parameters = list(request.names, first.parameters)?;
        let primary = derived.types.first().ok_or(ResourceError::Invariant)?.name;
        let mut recursor_parameters = None;
        for recursor in request.recursors {
            if same(work.names, recursor.name, primary, work.budget)?
                && recursor_parameters
                    .replace(list(request.names, recursor.parameters)?)
                    .is_some()
            {
                return Err(Stop::Unsupported);
            }
        }
        let recursor_parameters = recursor_parameters.ok_or(Stop::Unsupported)?;
        let mut restorer = restore::Restorer::new(self, parameters);
        let mut constructors = Vec::new();
        let mut members = Vec::new();
        let result = (|| {
            restorer.prepare(first.name, request, work, environment)?;
            for &index in &order.families {
                push(
                    &mut members,
                    request.types[index as usize].name,
                    work.budget,
                )?;
            }
            for &root in &self.original_constructors {
                push(&mut constructors, restorer.root(root, work)?, work.budget)?;
            }
            for (index, row) in derived.types.iter_mut().enumerate() {
                row.ty = restorer.root(row.ty, work)?;
                if index >= order.families.len() {
                    row.name = restorer.recursor(index - order.families.len())?;
                }
            }
            for row in &mut derived.rules {
                row.constructor = restorer.constructor(row.constructor, work)?;
                row.rhs = restorer.root(row.rhs, work)?;
                row.ty = restorer.root(row.ty, work)?;
            }
            let old = derived.phase.take().ok_or(ResourceError::Invariant)?;
            let checkpoint = derived.checkpoint.take().ok_or(ResourceError::Invariant)?;
            environment.retire_signature_stage(checkpoint, old, work.names, work.budget)?;
            let checkpoint = environment.signature_stage_checkpoint()?;
            // All restored syntax exists before the capability freezes its pool.
            // The imported expression/level bounds are never widened.
            let mut phase = environment.begin_auxiliary_stage(
                ends.0,
                ends.1,
                work.expressions,
                work.levels,
                work.budget,
            )?;
            for &index in &order.families {
                let family = &request.types[index as usize];
                phase = environment.stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Inductive,
                        name: family.name,
                        parameters,
                        ty: family.ty,
                        all: &members,
                    },
                    work.names,
                    work.budget,
                )?;
            }
            let scope = |phase: Formation, parameters| Scope {
                parameters,
                before: phase.before(),
                mode: Mode::Safe,
                expression_end: ends.0,
                level_end: ends.1,
                formation: Some(phase),
            };
            for (offset, &index) in order.constructors.iter().enumerate() {
                let constructor = &request.constructors[index as usize];
                let ty = *constructors.get(offset).ok_or(ResourceError::Invariant)?;
                if !scheme::matches(work, ty, constructor.ty)? {
                    return Err(Stop::Unsupported);
                }
                work.check_root_scope(parameters, &[ty])?;
                work.check_type(
                    ty,
                    false,
                    ReductionPath::start(),
                    scope(phase, parameters),
                    environment,
                )?;
                phase = environment.stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Constructor,
                        name: constructor.name,
                        parameters,
                        ty,
                        all: &members,
                    },
                    work.names,
                    work.budget,
                )?;
            }
            // Types contain no recursor calls, so none gains authority from an
            // unchecked sibling. Stage only after every restored type checks.
            for row in &derived.types {
                work.check_root_scope(recursor_parameters, &[row.ty])?;
                work.check_type(
                    row.ty,
                    false,
                    ReductionPath::start(),
                    scope(phase, recursor_parameters),
                    environment,
                )?;
            }
            for row in &derived.types {
                phase = environment.stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Recursor,
                        name: row.name,
                        parameters: recursor_parameters,
                        ty: row.ty,
                        all: &members,
                    },
                    work.names,
                    work.budget,
                )?;
            }
            for row in &derived.rules {
                work.check_root_scope(recursor_parameters, &[row.ty, row.rhs])?;
                work.check_type(
                    row.ty,
                    false,
                    ReductionPath::start(),
                    scope(phase, recursor_parameters),
                    environment,
                )?;
                let actual = work.infer_at(
                    row.rhs,
                    ReductionPath::start(),
                    scope(phase, recursor_parameters),
                    environment,
                )?;
                if !scheme::matches(work, actual.ty, row.ty)? {
                    // A generated-template mismatch cannot reject the input.
                    return Err(Stop::Unsupported);
                }
            }
            Ok((phase, checkpoint))
        })()
        .map_err(super::validation::generated_failure);
        // Generated rechecking cannot reject imported syntax. Export metadata
        // matching starts only after that boundary has completed successfully.
        let result = result.and_then(|(phase, checkpoint)| {
            self.match_export(request, order, derived, recursor_parameters, work)?;
            derived.phase = Some(phase);
            derived.checkpoint = Some(checkpoint);
            Ok(())
        });
        restorer.retire(work.budget)?;
        release(constructors, work.budget)?;
        release(members, work.budget)?;
        result
    }
}
