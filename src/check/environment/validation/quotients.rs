//! Independently derived quartet and exact descriptor confirmation.
use super::*;
use crate::check::environment::{
    Formation, SignatureKind, StoredKind, TypeSource,
    quotient::{Package, schema},
};
use crate::decode::primitive_decode::{
    ordinary_session::Working,
    quotients::{Request as QuotientRequest, Role},
};
use crate::syntax::expressions::ExprId;
use crate::syntax::levels::{LevelId, LevelKind, LevelNames, NameId};
use crate::syntax::names::Names;
use std::num::NonZeroU8;

#[cfg(feature = "introspection")]
fn capture_result(
    result: &Result<Admission, FailureReport>,
    request: &QuotientRequest<'_>,
    ordinal: u64,
    expected_ordinal: Option<u64>,
    decoder: &Decoder,
    budget: &mut Budget,
) {
    use crate::check::diagnostic::Sources;
    use crate::report::failure_snapshot::{
        Capture, Identity, Invariant, InvariantEvidence, Role as IdentityRole, Rule, Snapshot,
        Value, ValueRole,
    };
    if budget.failure_snapshot().is_some_and(Snapshot::has_rules)
        || matches!(result, Ok(Admission::Installed))
    {
        return;
    }
    let rule = match result {
        Ok(Admission::Duplicate) => Rule::Publication,
        Ok(Admission::TypeMismatch) => Rule::ExportMatch,
        Err(_) if expected_ordinal.is_some_and(|expected| expected != ordinal) => {
            Rule::DeclarationPolicy
        }
        Err(_) => Rule::QuotientValidation,
        Ok(Admission::Installed) => unreachable!(),
    };
    let values = [
        Value {
            role: ValueRole::Expected,
            value: expected_ordinal.unwrap_or(0),
        },
        Value {
            role: ValueRole::Actual,
            value: ordinal,
        },
    ];
    let invariant =
        matches!(result, Err(failure) if failure.code == "internal.invariant").then(|| {
            expected_ordinal
                .filter(|&expected| expected != ordinal)
                .map_or(
                    InvariantEvidence {
                        invariant: Invariant::Unavailable,
                        values: &[],
                    },
                    |_| InvariantEvidence {
                        invariant: Invariant::DeclarationSequence,
                        values: &values,
                    },
                )
        });
    let (names, levels, expressions) = decoder.syntax();
    budget.capture_failure(Snapshot::capture(Capture {
        declaration: Some(request.name),
        rules: &[rule],
        identities: &[
            Identity::name(IdentityRole::Declaration, request.name),
            Identity::expression(IdentityRole::Type, request.ty),
        ],
        invariant,
        delayed: None,
        mismatch: None,
        sources: Sources {
            expressions,
            levels,
            names,
            locals: None,
        },
    }));
}

fn same(a: NameId, z: NameId, names: &Names, b: &mut Budget) -> Result<bool, ResourceError> {
    Ok(names.summary(a, b)?.canonical == names.summary(z, b)?.canonical)
}
fn parameters(role: Role, names: &[NameId; 7]) -> &[NameId] {
    &names[5..5 + role.arity()]
}
fn argument_levels(work: &mut Working<'_>, parameters: &[NameId]) -> Result<[LevelId; 2], Stop> {
    let mut levels = [LevelId::ZERO; 2];
    for (target, &name) in levels.iter_mut().zip(parameters) {
        *target = work
            .levels
            .append(LevelKind::Param(name), work.names, work.budget)?;
    }
    Ok(levels)
}
fn matches_descriptor(
    work: &mut Working<'_>,
    names: &[NameId; 7],
    request: &QuotientRequest<'_>,
) -> Result<bool, Stop> {
    if !same(
        request.name,
        names[request.role.index() + 1],
        work.names,
        work.budget,
    )? || request.parameters.len() != request.role.arity()
    {
        return Ok(false);
    }
    for (&actual, &expected) in request
        .parameters
        .iter()
        .zip(parameters(request.role, names))
    {
        if !same(actual, expected, work.names, work.budget)? {
            return Ok(false);
        }
    }
    let arguments = argument_levels(work, parameters(request.role, names))?;
    let expected = schema::build(
        request.role,
        names,
        &arguments[..request.role.arity()],
        work.expressions,
        work.levels,
        work.names,
        work.budget,
    )?;
    schema_match::matches(work, expected, request.ty)
}
impl State {
    pub(crate) fn check_quotient(
        &mut self,
        request: &QuotientRequest<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
    ) -> Result<Admission, FailureReport> {
        if let Some(failure) = self.failure {
            return Err(failure);
        }
        self.failure = Some(ResourceError::Invariant.failure_report());
        budget.begin_declaration(ordinal, request.name, decoder.syntax().0);
        #[cfg(feature = "introspection")]
        let expected_ordinal = self.checked.checked_add(1);
        let result = self.quotient_inner(request, ordinal, decoder, budget);
        #[cfg(feature = "introspection")]
        capture_result(&result, request, ordinal, expected_ordinal, decoder, budget);
        budget.switch_bucket(crate::resource::Bucket::Input);
        if matches!(result, Ok(Admission::Installed)) {
            self.failure = None;
        } else if let Err(failure) = result {
            self.failure = Some(failure);
        }
        result
    }
    fn quotient_inner(
        &mut self,
        request: &QuotientRequest<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
    ) -> Result<Admission, FailureReport> {
        budget
            .charge_work(1)
            .map_err(ResourceError::failure_report)?;
        let next = self
            .checked
            .checked_add(1)
            .ok_or_else(|| ResourceError::Counter.failure_report())?;
        if ordinal != next || self.environment.stage.is_some() {
            return Err(ResourceError::Invariant.failure_report());
        }
        let old = self.environment.quotient;
        let names = match old {
            Some(p) => p.names,
            None => decoder
                .quotient_names(budget)
                .map_err(ResourceError::failure_report)?,
        };
        if let Some(package) = old {
            if same(
                request.name,
                names[request.role.index() + 1],
                decoder.syntax().0,
                budget,
            )
            .map_err(ResourceError::failure_report)?
                && package.seen.get() & request.role.mask() != 0
            {
                return Ok(Admission::Duplicate);
            }
        } else {
            let eq = self.eq_signature(names[0], decoder, budget)?;
            let Some((ty, ctor, parameter, ctor_parameter)) = eq else {
                return Ok(Admission::TypeMismatch);
            };
            let mut matched = false;
            let negative = decoder
                .declaration_session(budget, |work| {
                    let u =
                        work.levels
                            .append(LevelKind::Param(parameter), work.names, work.budget)?;
                    let expected =
                        schema::eq_type(u, work.expressions, work.levels, work.names, work.budget)?;
                    if !schema_match::matches(work, expected, ty)? {
                        return Ok(());
                    }
                    let ctor_u = work.levels.append(
                        LevelKind::Param(ctor_parameter),
                        work.names,
                        work.budget,
                    )?;
                    let expected = schema::eq_constructor(
                        names[0],
                        ctor_u,
                        work.expressions,
                        work.levels,
                        work.names,
                        work.budget,
                    )?;
                    matched = schema_match::matches(work, expected, ctor)?;
                    Ok(())
                })
                .map_err(|e| e.failure_report())?;
            if negative.is_some() {
                return Err(ResourceError::Invariant.failure_report());
            }
            if !matched {
                return Ok(Admission::TypeMismatch);
            }
            for &name in &names[1..5] {
                if self
                    .environment
                    .lookup(name, self.environment.len(), decoder.syntax().0, budget)
                    .map_err(ResourceError::failure_report)?
                    .is_some()
                {
                    return Ok(Admission::Duplicate);
                }
            }
        }
        let mut matched = false;
        let negative = decoder
            .declaration_session(budget, |work| {
                matched = matches_descriptor(work, &names, request)?;
                Ok(())
            })
            .map_err(|e| e.failure_report())?;
        if negative.is_some() {
            return Err(ResourceError::Invariant.failure_report());
        }
        if !matched {
            return Ok(Admission::TypeMismatch);
        }
        let seen = NonZeroU8::new(old.map_or(0, |p| p.seen.get()) | request.role.mask())
            .ok_or_else(|| ResourceError::Invariant.failure_report())?;
        if old.is_none() {
            self.environment.quotient = Some(Package { names, seen });
            let (_, levels, expressions) = decoder.syntax();
            let (expression_end, level_end) = (expressions.len(), levels.len());
            let mut phase = self
                .environment
                .begin_stage(expression_end, level_end, budget)
                .map_err(ResourceError::failure_report)?;
            for role in [Role::Type, Role::Constructor, Role::Lift, Role::Induction] {
                self.check_quotient_schema(
                    role,
                    &names,
                    phase,
                    expression_end,
                    level_end,
                    decoder,
                    budget,
                )?;
                phase = self
                    .environment
                    .stage_quotient(phase, role, decoder.syntax().0, budget)
                    .map_err(ResourceError::failure_report)?;
            }
            self.environment
                .prepare_quotient_commit(phase, budget)
                .map_err(ResourceError::failure_report)?
                .commit();
            budget.observe(Event::DeclarationsInstalled, 4);
        } else {
            // Confirmation installs nothing and changes no stored signature.
            self.environment.quotient = Some(Package { names, seen });
        }
        self.checked = next;
        budget.checked_declarations(next);
        Ok(Admission::Installed)
    }
    fn eq_signature(
        &self,
        name: NameId,
        decoder: &Decoder,
        budget: &mut Budget,
    ) -> Result<Option<(ExprId, ExprId, NameId, NameId)>, FailureReport> {
        let names = decoder.syntax().0;
        let Some(eq) = self
            .environment
            .lookup(name, self.environment.len(), names, budget)
            .map_err(ResourceError::failure_report)?
        else {
            return Ok(None);
        };
        if eq.kind != StoredKind::Signature(SignatureKind::Inductive) || eq.parameters.len() != 1 {
            return Ok(None);
        }
        let TypeSource::Original(ty) = eq.ty else {
            return Err(ResourceError::Invariant.failure_report());
        };
        let Some(family) = self
            .environment
            .inductive(name, self.environment.len(), names, budget)
            .map_err(ResourceError::failure_report)?
        else {
            return Err(ResourceError::Invariant.failure_report());
        };
        if family.constructors.len() != 1 {
            return Ok(None);
        }
        let ctor_name = family.constructors[0].constructor;
        let ctor = self
            .environment
            .lookup(ctor_name, self.environment.len(), names, budget)
            .map_err(ResourceError::failure_report)?
            .ok_or_else(|| ResourceError::Invariant.failure_report())?;
        let TypeSource::Original(ctor_ty) = ctor.ty else {
            return Err(ResourceError::Invariant.failure_report());
        };
        if ctor.kind != StoredKind::Signature(SignatureKind::Constructor) {
            return Err(ResourceError::Invariant.failure_report());
        }
        if ctor.parameters.len() != 1 {
            return Ok(None);
        }
        Ok(Some((ty, ctor_ty, eq.parameters[0], ctor.parameters[0])))
    }
    #[allow(clippy::too_many_arguments)]
    fn check_quotient_schema(
        &self,
        role: Role,
        names: &[NameId; 7],
        phase: Formation,
        expression_end: usize,
        level_end: usize,
        decoder: &mut Decoder,
        budget: &mut Budget,
    ) -> Result<(), FailureReport> {
        let negative = decoder
            .declaration_session(budget, |work| {
                let params = parameters(role, names);
                let arguments = argument_levels(work, params)?;
                let expected = schema::build(
                    role,
                    names,
                    &arguments[..role.arity()],
                    work.expressions,
                    work.levels,
                    work.names,
                    work.budget,
                )?;
                work.check_root_scope(params, &[expected])?;
                work.check_type(
                    expected,
                    false,
                    ReductionPath::start(),
                    Scope {
                        formation: Some(phase),
                        parameters: params,
                        before: phase.before(),
                        mode: Mode::Safe,
                        expression_end,
                        level_end,
                    },
                    &self.environment,
                )?;
                Ok(())
            })
            .map_err(|e| e.failure_report())?;
        if negative.is_some() {
            return Err(ResourceError::Invariant.failure_report());
        }
        Ok(())
    }
}
