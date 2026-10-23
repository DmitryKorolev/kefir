//! Type formation for owned expanded templates, never an admission result.
//! All generated-root failures return to the terminal outer owner. No inferred
//! fact, auxiliary signature or phase token can outlive that owner.
use super::*;
use crate::check::environment::SignatureStageCheckpoint;
use crate::syntax::levels::ScopeError;

impl Queue {
    pub(super) fn check_constructor_names(
        &self,
        work: &mut Working<'_>,
        environment: &Environment,
    ) -> Result<(), Stop> {
        // A prior declaration cannot capture a generated symbolic constructor.
        // Current input names already passed the reserved-namespace scan.
        for constructor in &self.constructors {
            if environment
                .lookup(
                    constructor.helper,
                    environment.len(),
                    work.names,
                    work.budget,
                )?
                .is_some()
            {
                return Err(Stop::Unsupported);
            }
        }
        Ok(())
    }
    #[allow(clippy::too_many_arguments)]
    pub(in super::super) fn check_expanded_types(
        &self,
        request: &Request<'_>,
        order: &Order,
        work: &mut Working<'_>,
        environment: &mut Environment,
        phase: Formation,
        checkpoint: SignatureStageCheckpoint,
        ends: (usize, usize),
        publication: &mut Publication,
    ) -> Result<(), Stop> {
        let first = request.types.first().ok_or(ResourceError::Invariant)?;
        let parameters = list(request.names, first.parameters)?;
        let scope = |phase: Formation| Scope {
            parameters,
            before: phase.before(),
            mode: Mode::Safe,
            expression_end: ends.0,
            level_end: ends.1,
            formation: Some(phase),
        };
        // Discovery precedes all helper rewriting: recipes still mention only
        // committed declarations and original family signatures. Check each
        // saved dropped application once before expanded authority can hide it.
        // Closure checks it in its complete common parameter telescope; a
        // helper body has no inherited checkedness certificate here.
        if first.num_params != 0 {
            for key in &self.keys {
                work.check_root_scope(parameters, &[key.root])
                    .map_err(generated_failure)?;
                work.infer_at(key.root, ReductionPath::start(), scope(phase), environment)
                    .map_err(generated_failure)?;
            }
        }
        // Originals already passed family type formation against the committed
        // prefix. Helpers are independently rechecked while only those original
        // signatures are visible; no helper can justify another helper's type.
        for family in &self.families {
            check_type(family.ty, scope(phase), work, environment)?;
        }
        environment.retire_signature_stage(checkpoint, phase, work.names, work.budget)?;
        let checkpoint = environment.signature_stage_checkpoint()?;
        let mut members = Vec::new();
        let mut derived = recursors::Derived::default();
        let result = (|| {
            for &index in &order.families {
                push(
                    &mut members,
                    request.types[index as usize].name,
                    work.budget,
                )?;
            }
            for family in &self.families {
                push(&mut members, family.helper, work.budget)?;
            }
            // Freeze generated lookup bounds separately from the imported
            // frontiers. This capability grants signature typing only.
            let mut phase = environment.begin_auxiliary_stage(
                ends.0,
                ends.1,
                work.expressions,
                work.levels,
                work.budget,
            )?;
            for (name, ty) in order
                .families
                .iter()
                .map(|&index| {
                    let family = &request.types[index as usize];
                    (family.name, family.ty)
                })
                .chain(
                    self.families
                        .iter()
                        .map(|family| (family.helper, family.ty)),
                )
            {
                phase = environment.stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Inductive,
                        name,
                        parameters,
                        ty,
                        all: &members,
                    },
                    work.names,
                    work.budget,
                )?;
            }
            if self.original_constructors.len() != order.constructors.len() {
                return Err(ResourceError::Invariant.into());
            }
            let expanded = expanded::Expanded::new(self, request, order)?;
            self.check_constructor_names(work, environment)?;
            for &root in &self.original_constructors {
                work.check_root_scope(parameters, &[root])
                    .map_err(generated_failure)?;
            }
            for constructor in &self.constructors {
                work.check_root_scope(parameters, &[constructor.ty])
                    .map_err(generated_failure)?;
            }
            if !expanded.raw(work)? {
                return Err(Stop::Unsupported);
            }
            with_scratch(work, |work, scratch| {
                scratch
                    .family(work, &expanded, scope(phase), environment)
                    .map_err(generated_derivation_failure)?;
                if !scratch
                    .constructors(work, &expanded, scope(phase), environment)
                    .map_err(generated_derivation_failure)?
                {
                    return Err(Stop::Unsupported);
                }
                recursors::derive(
                    &expanded,
                    request,
                    scratch,
                    work,
                    environment,
                    scope(phase),
                    checkpoint,
                    &mut derived,
                )
                .map_err(generated_failure)?;
                Ok(())
            })?;
            self.restore_and_recheck(request, order, &mut derived, work, environment, ends)?;
            self.capture_publication(request, order, &mut derived, publication, work, environment)?;
            // No metadata, recursor or admission certificate is prepared here.
            // The outer terminal owner retires this entire auxiliary stage
            // before the expression session is rolled back.
            Ok(())
        })();
        derived.retire(work.budget)?;
        release(members, work.budget)?;
        result
    }
}
fn check_type(
    root: ExprId,
    scope: Scope<'_>,
    work: &mut Working<'_>,
    environment: &Environment,
) -> Result<(), Stop> {
    work.check_root_scope(scope.parameters, &[root])
        .map_err(generated_failure)?;
    work.check_type(root, false, ReductionPath::start(), scope, environment)
        .map(|_| ())
        .map_err(generated_failure)
}
pub(super) fn generated_failure(error: Stop) -> Stop {
    match error {
        Stop::Judgment(_) => ResourceError::Invariant.into(),
        Stop::Scope(ScopeError::DuplicateParameter(_)) => Stop::Unsupported,
        // Required lookup failures remain inconclusive observations about our
        // generated syntax, never MissingConstant/UnsafeReference rejections.
        Stop::Inference(error) => Stop::Observation(error),
        other => other,
    }
}

// A negative judgment about the translated block is not yet a justified public
// judgment about the input: restoration/computation preservation is unfinished.
fn generated_derivation_failure(error: Stop) -> Stop {
    match error {
        Stop::Judgment(_) => Stop::Unsupported,
        other => generated_failure(other),
    }
}
