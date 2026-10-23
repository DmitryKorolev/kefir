//! Original typing precedes nested translation: discarded arguments
//! remain obligations. Public admission follows complete expanded checking,
//! exact restoration/matching and successful retirement of every private owner.
//! Raw uniformity of block-family occurrences in constructor types precedes
//! translation, matching the reference kernel's pre-elimination scan.
use super::*;
use crate::decode::primitive_decode::ordinary_session::Negative;
use std::mem::size_of;
mod publication;
mod queue;
mod templates;
use publication::Publication;
use templates::Order;

impl State {
    pub(super) fn check_original_nested(
        &mut self,
        request: &Request<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
    ) -> Result<Admission, FailureReport> {
        let resource = ResourceError::failure_report;
        let mut retired = false;
        let mut installed = false;
        let mut publication = Publication::default();
        let result = (|| {
            budget.charge_work(32).map_err(resource)?;
            if self.checked.checked_add(1) != Some(ordinal) {
                return Err(resource(ResourceError::Invariant));
            }
            if request.types.iter().any(|f| f.is_unsafe)
                || request.constructors.iter().any(|c| c.is_unsafe)
                || request.recursors.iter().any(|r| r.is_unsafe)
            {
                return Err(unsupported());
            }
            // One owner keeps generated syntax alive throughout original and
            // expanded checking. Only imported associations can cross cleanup.
            let mut duplicate = false;
            let result = decoder.declaration_session(budget, |work| {
                let operation = self.original_nested_in_session(
                    request,
                    work,
                    &mut duplicate,
                    &mut publication,
                );
                // Failed routes retire the entire terminal environment before
                // syntax cleanup. A ready route already retired every auxiliary
                // stage and retains only the unchanged committed prefix.
                if operation.is_err() || !publication.ready {
                    let environment = std::mem::take(&mut self.environment);
                    retired = true;
                    let retirement = environment.retire(work.budget);
                    work.record_nested_retirement(retirement);
                }
                operation
            });
            match result {
                Ok(Some(_)) => Ok(Admission::TypeMismatch),
                Ok(None) if duplicate => Ok(Admission::Duplicate),
                Ok(None) if publication.ready => {
                    let count = publication
                        .families
                        .len()
                        .checked_add(publication.constructors.len())
                        .and_then(|n| n.checked_add(publication.recursors.len()))
                        .ok_or_else(|| resource(ResourceError::Counter))?;
                    let plan = std::mem::take(&mut publication);
                    let prepared = plan.prepare(request, &mut self.environment, decoder, budget);
                    plan.retire(budget).map_err(resource)?;
                    let prepared = prepared.map_err(resource)?;
                    prepared.commit();
                    self.checked = ordinal;
                    budget.checked_declarations(ordinal);
                    budget.observe(Event::DeclarationsInstalled, count as u64);
                    installed = true;
                    Ok(Admission::Installed)
                }
                Ok(None) => Err(resource(ResourceError::Invariant)),
                Err(error) => Err(error.failure_report()),
            }
        })();
        let cleanup = if installed {
            Ok(())
        } else {
            publication.retire(budget)
        };
        if !retired && !installed {
            // Setup, session cleanup or public preflight failed. No generated
            // reference remains here; the terminal environment still retires.
            if let Err(cleanup) = std::mem::take(&mut self.environment).retire(budget)
                && !matches!(result, Err(error) if error.outcome == crate::resource::failure::FailureOutcome::InternalError)
            {
                return Err(resource(cleanup));
            }
        }
        cleanup.map_err(resource)?;
        result
    }

    fn original_nested_in_session(
        &mut self,
        request: &Request<'_>,
        work: &mut Working<'_>,
        duplicate: &mut bool,
        publication: &mut Publication,
    ) -> Result<(), Stop> {
        let before = self.environment.len();
        let expression_end = work.expressions.len();
        let level_end = work.levels.len();
        let scope = |parameters, formation: Option<Formation>| Scope {
            parameters,
            before: formation.map_or(before, |p| p.before()),
            mode: Mode::Safe,
            expression_end,
            level_end,
            formation,
        };
        // Family types see only committed declarations, never another unchecked
        // member. The subsequent signature phase grants typing only.
        for family in request.types {
            let parameters = list(request.names, family.parameters)?;
            work.check_root_scope(parameters, &[family.ty])?;
            work.check_type(
                family.ty,
                false,
                ReductionPath::start(),
                scope(parameters, None),
                &self.environment,
            )?;
        }
        let mut names = Vec::new();
        let mut order = Order::default();
        let result = (|| {
            work.budget.grow_vec(&mut names, request.types.len())?;
            for family in request.types {
                names.push(family.name);
            }
            let checkpoint = self.environment.signature_stage_checkpoint()?;
            let mut phase = self
                .environment
                .begin_stage(expression_end, level_end, work.budget)?;
            for family in request.types {
                if self
                    .environment
                    .lookup_visible(
                        family.name,
                        phase.before(),
                        Some(phase),
                        work.names,
                        work.budget,
                    )?
                    .is_some()
                {
                    *duplicate = true;
                    return Ok(());
                }
                phase = self.environment.stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Inductive,
                        name: family.name,
                        parameters: list(request.names, family.parameters)?,
                        ty: family.ty,
                        all: &names,
                    },
                    work.names,
                    work.budget,
                )?;
            }
            for constructor in request.constructors {
                let parameters = list(request.names, constructor.parameters)?;
                work.check_root_scope(parameters, &[constructor.ty])?;
                work.check_type(
                    constructor.ty,
                    false,
                    ReductionPath::start(),
                    scope(parameters, Some(phase)),
                    &self.environment,
                )?;
            }
            // Reference-kernel raw uniformity (inductive.cpp
            // check_uniform_ind_occs): every occurrence of a block family in a
            // constructor type must be applied exactly to the block's level
            // parameters and parameter binders, observed on raw syntax before
            // nested elimination. The translation queue cannot classify
            // occurrences; a completed non-uniform observation here rejects the
            // block instead of translating it. Scan failures that cannot
            // classify stay declines through the ordinary Stop mapping.
            let mut uniform = true;
            families::with_set(
                work,
                request.types.iter().map(|family| family.name),
                |work, members| {
                    for family in request.types {
                        let level_parameters = list(request.names, family.parameters)?;
                        for constructor in request.constructors {
                            work.budget.charge_work(1)?;
                            if !same(work.names, constructor.inductive, family.name, work.budget)? {
                                continue;
                            }
                            if !raw_constructor(
                                work,
                                family,
                                members,
                                request.types,
                                level_parameters,
                                constructor.ty,
                            )? {
                                #[cfg(feature = "introspection")]
                                capture_work(
                                    work,
                                    family.name,
                                    &[crate::report::failure_snapshot::Rule::ConstructorValidation],
                                    &[
                                        crate::report::failure_snapshot::Identity::name(
                                            crate::report::failure_snapshot::Role::Declaration,
                                            constructor.name,
                                        ),
                                        crate::report::failure_snapshot::Identity::expression(
                                            crate::report::failure_snapshot::Role::Type,
                                            constructor.ty,
                                        ),
                                    ],
                                );
                                uniform = false;
                                return Ok(());
                            }
                        }
                    }
                    Ok(())
                },
            )?;
            if !uniform {
                return Err(Stop::Judgment(Negative::TypeMismatch));
            }
            order.build(request, work)?;
            let mut queue = queue::Queue::default();
            let expansion = queue
                .run(
                    request,
                    &order,
                    work,
                    &self.environment,
                    before,
                    phase,
                    (expression_end, level_end),
                )
                .and_then(|()| {
                    queue.check_expanded_types(
                        request,
                        &order,
                        work,
                        &mut self.environment,
                        phase,
                        checkpoint,
                        (expression_end, level_end),
                        publication,
                    )
                });
            let retirement = queue.retire(work.budget);
            work.record_nested_retirement(retirement);
            expansion?;
            Ok(())
        })();
        let retirement = order.retire(work.budget);
        work.record_nested_retirement(retirement);
        let bytes = names.capacity() * std::mem::size_of::<NameId>();
        drop(names);
        let retirement = work.budget.release(bytes as u64);
        work.record_nested_retirement(retirement);
        result
    }
}
