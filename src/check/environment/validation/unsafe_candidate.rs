//! Unsafe ordinary definitions have a private full-body candidate, never a stub.
use super::*;

impl State {
    pub(super) fn check_unsafe_candidate(
        &mut self,
        request: &Request<'_>,
        next: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
    ) -> Result<Admission, FailureReport> {
        let value = request.value.ok_or_else(unsupported)?;
        let before = self.environment.len();
        let expression_end = decoder.syntax().2.len();
        let level_end = decoder.syntax().1.len();
        let prior = Scope {
            formation: None,
            parameters: request.parameters,
            before,
            mode: Mode::Unsafe,
            expression_end,
            level_end,
        };
        let mut type_path = None;
        let negative = decoder
            .declaration_session(budget, |work| {
                let result = (|| {
                    work.check_input_scope(request.parameters, &[request.ty, value])?;
                    type_path = Some(work.check_type(
                        request.ty,
                        false,
                        ReductionPath::start(),
                        prior,
                        &self.environment,
                    )?);
                    Ok(())
                })();
                #[cfg(feature = "introspection")]
                if let Err(error) = result {
                    capture_ordinary(work, request, error, request.ty, Some(value), None);
                }
                result
            })
            .map_err(|error| error.failure_report())?;
        if negative.is_some() {
            return Ok(Admission::TypeMismatch);
        }
        let type_path = type_path.ok_or_else(|| ResourceError::Invariant.failure_report())?;
        let phase = self
            .environment
            .stage_unsafe_candidate(
                request,
                expression_end,
                level_end,
                decoder.syntax().0,
                budget,
            )
            .map_err(ResourceError::failure_report)?;
        // A fresh session prevents header-only inference/comparison caches from
        // crossing into the context where the full candidate is visible.
        let candidate = Scope {
            formation: Some(phase),
            before: phase.before(),
            ..prior
        };
        let negative = decoder
            .declaration_session(budget, |work| {
                #[cfg(feature = "introspection")]
                let mut compared = None;
                let result = (|| {
                    work.check_input_scope(request.parameters, &[request.ty, value])?;
                    let inferred =
                        work.infer_at(value, ReductionPath::start(), candidate, &self.environment)?;
                    #[cfg(feature = "introspection")]
                    {
                        compared = Some(crate::report::failure_snapshot::Mismatch {
                            expected: request.ty,
                            actual: inferred.ty,
                        });
                    }
                    work.compare_checked_types(
                        inferred.ty,
                        request.ty,
                        type_path.maximum(inferred.path),
                        candidate,
                        &self.environment,
                    )?;
                    Ok(())
                })();
                #[cfg(feature = "introspection")]
                if let Err(error) = result {
                    capture_ordinary(work, request, error, request.ty, Some(value), compared);
                }
                result
            })
            .map_err(|error| error.failure_report())?;
        if negative.is_some() {
            return Ok(Admission::TypeMismatch);
        }
        self.environment
            .prepare_unsafe_commit(phase, budget)
            .map_err(ResourceError::failure_report)?
            .commit();
        // Infallible publication tail; no axiom or annotation certificate exists
        // for an unsafe definition. State.check supplies terminal failure poison.
        self.checked = next;
        budget.checked_declarations(next);
        budget.observe(Event::DeclarationsInstalled, 1);
        Ok(Admission::Installed)
    }
}
