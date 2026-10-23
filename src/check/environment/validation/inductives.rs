//! Safe single families with nonrecursive constructors.
//! Broader specifications decline. Exported recursors supply no authority.
use super::{Admission, State, unsupported};
use crate::check::environment::normalization::{Mode, Scope};
use crate::check::environment::{SignatureInput, SignatureKind};
use crate::decode::primitive_decode::{
    Decoder,
    inductives::{Request, Span},
    ordinary_session::{Stop, Working},
};
use crate::resource::{Budget, Event, ReductionPath, ResourceError, failure::FailureReport};
use crate::syntax::expressions::{BinderInfo, ExprId, ExprKind};
use crate::syntax::levels::{LevelKind, LevelNames, NameId};
use crate::syntax::names::{Component, Names};

#[cfg(feature = "introspection")]
fn capture(
    request: &Request<'_>,
    decoder: &Decoder,
    budget: &mut Budget,
    rules: &[crate::report::failure_snapshot::Rule],
    identities: &[crate::report::failure_snapshot::Identity],
    invariant: Option<crate::report::failure_snapshot::InvariantEvidence<'_>>,
) {
    use crate::check::diagnostic::Sources;
    use crate::report::failure_snapshot::{Capture, Snapshot};
    if budget.failure_snapshot().is_some_and(Snapshot::has_rules) {
        return;
    }
    let (names, levels, expressions) = decoder.syntax();
    budget.capture_failure(Snapshot::capture(Capture {
        declaration: request.types.first().map(|family| family.name),
        rules,
        identities,
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

#[cfg(feature = "introspection")]
fn capture_result(
    result: &Result<Admission, FailureReport>,
    request: &Request<'_>,
    ordinal: u64,
    expected_ordinal: Option<u64>,
    decoder: &Decoder,
    budget: &mut Budget,
) {
    use crate::report::failure_snapshot::{
        Identity, Invariant, InvariantEvidence, Role, Rule, Value, ValueRole,
    };
    if budget
        .failure_snapshot()
        .is_some_and(crate::report::failure_snapshot::Snapshot::has_rules)
        || matches!(result, Ok(Admission::Installed))
    {
        return;
    }
    let family = request.types.first();
    let rule = match result {
        Ok(Admission::Duplicate) => Rule::Publication,
        Err(failure) if failure.code == "support.policy" => Rule::DeclarationPolicy,
        _ => Rule::ConstructorValidation,
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
    let invariant = matches!(result, Err(failure) if failure.code == "internal.invariant")
        .then_some(expected_ordinal)
        .flatten()
        .filter(|&expected| expected != ordinal)
        .map(|_| InvariantEvidence {
            invariant: Invariant::DeclarationSequence,
            values: &values,
        })
        .or_else(|| {
            matches!(result, Err(failure) if failure.code == "internal.invariant").then_some(
                InvariantEvidence {
                    invariant: Invariant::Unavailable,
                    values: &[],
                },
            )
        });
    if let Some(family) = family {
        capture(
            request,
            decoder,
            budget,
            &[rule],
            &[
                Identity::name(Role::Declaration, family.name),
                Identity::expression(Role::Type, family.ty),
            ],
            invariant,
        );
    } else {
        capture(request, decoder, budget, &[rule], &[], invariant);
    }
}

fn list(names: &[NameId], span: Span) -> Result<&[NameId], ResourceError> {
    let end = (span.start as usize)
        .checked_add(span.len as usize)
        .ok_or(ResourceError::Counter)?;
    names
        .get(span.start as usize..end)
        .ok_or(ResourceError::Invariant)
}
fn same(names: &Names, a: NameId, b: NameId, budget: &mut Budget) -> Result<bool, ResourceError> {
    Ok(names.summary(a, budget)?.canonical == names.summary(b, budget)?.canonical)
}
fn singleton(
    names: &Names,
    xs: &[NameId],
    name: NameId,
    budget: &mut Budget,
) -> Result<bool, ResourceError> {
    Ok(xs.len() == 1 && same(names, xs[0], name, budget)?)
}
fn suffix(
    names: &Names,
    name: NameId,
    prefix: NameId,
    text: &str,
    budget: &mut Budget,
) -> Result<bool, ResourceError> {
    match names.view(name, budget)? {
        Some((p, Component::String(s))) if s == text => same(names, p, prefix, budget),
        _ => Ok(false),
    }
}

impl State {
    pub(crate) fn check_inductive(
        &mut self,
        request: &Request<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
    ) -> Result<Admission, FailureReport> {
        if let Some(failure) = self.failure {
            return Err(failure);
        }
        self.failure = Some(ResourceError::Invariant.failure_report());
        budget.begin_declaration(ordinal, NameId::ANONYMOUS, decoder.syntax().0);
        #[cfg(feature = "introspection")]
        let expected_ordinal = self.checked.checked_add(1);
        let result = self.check_fieldless(request, ordinal, decoder, budget);
        #[cfg(feature = "introspection")]
        capture_result(&result, request, ordinal, expected_ordinal, decoder, budget);
        budget.switch_bucket(crate::resource::Bucket::Input);
        // Every non-installed result is terminal. Staged entries are inaccessible
        // through committed scopes and the owner can only report and retire.
        if matches!(result, Ok(Admission::Installed)) {
            self.failure = None;
        } else if let Err(failure) = result {
            self.failure = Some(failure);
        }
        result
    }
}

fn append(work: &mut Working<'_>, kind: ExprKind<'_>) -> Result<ExprId, Stop> {
    Ok(work
        .expressions
        .append(kind, work.levels, work.names, work.budget)?)
}

mod fieldless;
