//! One-sided expected-Sort evidence after completed checked full head exposure.
use super::*;

pub(super) enum NonSort {
    Proven,
    NotProven,
}

/// Construction invariant: `head` is the result of required FULL exposure of an
/// already inferred type, with this unchanged scope/context/environment. The
/// head owner completed constant-use/universe validation, major exposure, K and
/// structure guards and iota selection. Unsupported computation never returns
/// this premise. Raw syntax, Cheap/NonDelta heads and optional comparison failure
/// cannot call this classifier. Observation callers do not consume its result.
///
/// Rechecking the committed identity/frontier and exact arity narrows the result
/// to neutral recursors; it is not a general normal-form mismatch certificate.
/// `Environment::recursor` reads fully published metadata only, even during a
/// formation scope; private signatures cannot supply this evidence.
pub(super) fn completed_neutral_recursor(
    head: crate::check::environment::normalization::Head,
    work: &mut Working<'_>,
    scope: &Scope<'_>,
    environment: &Environment,
) -> Result<NonSort, Stop> {
    let mut root = head.expression;
    let mut arity = 0usize;
    loop {
        work.budget.charge_work(1)?;
        match work.expressions.get(root, work.budget)?.kind(
            work.expressions,
            work.levels,
            work.budget,
        )? {
            ExprKind::App(function, _) => {
                arity = arity.checked_add(1).ok_or(ResourceError::Counter)?;
                root = function;
            }
            ExprKind::Constant(name, _) if arity != 0 => {
                let Some(recursor) = environment.recursor(
                    name,
                    scope.before.min(environment.len()),
                    work.names,
                    work.budget,
                )?
                else {
                    return Ok(NonSort::NotProven);
                };
                let expected = (recursor.common_prefix as usize)
                    .checked_add(recursor.num_indices as usize)
                    .and_then(|n| n.checked_add(1))
                    .ok_or(ResourceError::Counter)?;
                return Ok(if arity == expected {
                    NonSort::Proven
                } else {
                    NonSort::NotProven
                });
            }
            _ => return Ok(NonSort::NotProven),
        }
    }
}
