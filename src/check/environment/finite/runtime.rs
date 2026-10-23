//! Call-local schema queries. Complete original certification grants referent
//! identity, never argument typing. The driver alone supplies the typed-source
//! premise; raw expression summaries and this module cannot mint it.
use super::*;
use crate::check::environment::normalization::{Mode, Scope};
use crate::syntax::expressions::ExprKind;
use crate::syntax::levels::LevelKind;

#[derive(Clone, Copy)]
pub(crate) enum Referent {
    Bool,
    False,
    True,
    Decidable,
    Consumer,
    Decide,
    Ball,
    Finite,
    FinMk,
    FinType,
    NaturalType,
    NaturalLt,
    Refl,
    SuccLt,
}
impl Referent {
    fn index(self) -> usize {
        match self {
            Self::Bool => 1,
            Self::False => 66,
            Self::True => 180,
            Self::Decidable => 2,
            Self::Decide => 60,
            Self::Consumer => 152,
            Self::Ball => 56,
            Self::Finite => 57,
            Self::FinMk => 132,
            Self::FinType => 6,
            Self::NaturalType => 12,
            Self::NaturalLt => 97,
            Self::Refl => 172,
            Self::SuccLt => 105,
        }
    }
}

/// Raw mapping only. This carries no checkedness until the private typed Head
/// owner authenticates that these are its exact saturated original arguments.
pub(crate) struct Request {
    pub source: ExprId,
    pub consumer: u32,
    pub operands: [ExprId; 4], // original proposition, bound, predicate, decision
    pub finite: bool,
    // Zero depth denotes the active application route; otherwise exact saved Iota.
    pub saved_end: u32,
    pub saved_depth: u32,
}

impl Environment {
    pub(crate) fn finite_available(&self, scope: &Scope<'_>) -> bool {
        self.finite.frontier != 0
            && self.finite.frontier as usize <= scope.before
            && scope.formation.is_none()
            && scope.mode == Mode::Safe
            && self.stage.is_none()
    }

    /// Original exact closure cannot be overwritten or shadowed. Resolve the
    /// canonical names through the existing index, then check committed lookup;
    /// no pin table of runtime handles or generated name is retained.
    pub(crate) fn finite_name(
        &self,
        referent: Referent,
        scope: &Scope<'_>,
        n: &Names,
        b: &mut Budget,
    ) -> Result<Option<NameId>, ResourceError> {
        if !self.finite_available(scope) {
            return Ok(None);
        }
        let mut path = [0u32; 8];
        let mut length = 0;
        let mut at = manifest::REFERENT_NAMES[referent.index()];
        while at != 0 {
            if length == path.len() {
                return Err(ResourceError::Invariant);
            }
            path[length] = at;
            length += 1;
            at = manifest::NAMES[at as usize - 1][0];
        }
        let mut name = NameId::ANONYMOUS;
        for &index in path[..length].iter().rev() {
            let [_, tag, a, c] = manifest::NAMES[index as usize - 1];
            if tag != 0 {
                return Err(ResourceError::Invariant);
            }
            let component =
                std::str::from_utf8(bytes(a, c)?).map_err(|_| ResourceError::Invariant)?;
            let Some(next) = n.find_component(name, Component::String(component), b)? else {
                return Err(ResourceError::Invariant);
            };
            name = next;
        }
        let signature = self
            .lookup(name, scope.before, n, b)?
            .ok_or(ResourceError::Invariant)?;
        if signature.slot.is_none() {
            return Err(ResourceError::Invariant);
        }
        Ok(Some(signature.name))
    }

    pub(crate) fn finite_named(
        &self,
        actual: NameId,
        referent: Referent,
        scope: &Scope<'_>,
        n: &Names,
        b: &mut Budget,
    ) -> Result<Option<u32>, ResourceError> {
        if !matching::name(manifest::REFERENT_NAMES[referent.index()], actual, n, b)? {
            return Ok(None);
        }
        let original = self
            .lookup(actual, scope.before, n, b)?
            .ok_or(ResourceError::Invariant)?;
        Ok(Some(original.slot.ok_or(ResourceError::Invariant)?))
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn finite_request(
        &self,
        source: ExprId,
        consumer: ExprId,
        arguments: &[ExprId],
        scope: &Scope<'_>,
        e: &Expressions,
        l: &Levels,
        n: &Names,
        b: &mut Budget,
    ) -> Result<Option<Request>, ResourceError> {
        self.finite_request_at(source, consumer, arguments, None, scope, e, l, n, b)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn finite_request_at(
        &self,
        source: ExprId,
        consumer: ExprId,
        arguments: &[ExprId],
        transported: Option<(ExprId, [ExprId; 3])>,
        scope: &Scope<'_>,
        e: &Expressions,
        l: &Levels,
        n: &Names,
        b: &mut Budget,
    ) -> Result<Option<Request>, ResourceError> {
        if !self.finite_available(scope) || arguments.len() != 5 {
            return Ok(None);
        }
        let ExprKind::Constant(name, universes) = e.get(consumer, b)?.kind(e, l, b)? else {
            return Ok(None);
        };
        let Some(slot) = self.finite_named(name, Referent::Consumer, scope, n, b)? else {
            return Ok(None);
        };
        if universes.len() != 1 {
            return Ok(None);
        }
        let LevelKind::Succ(zero) = l.get(universes[0], b)?.kind() else {
            return Ok(None);
        };
        if !matches!(l.get(zero, b)?.kind(), LevelKind::Zero) {
            return Ok(None);
        }
        b.charge_work(9)?;
        let [proposition, motive, false_minor, true_minor, instance] =
            arguments.as_array::<5>().ok_or(ResourceError::Invariant)?;
        // Exact raw Bool motive and proof-independent minors. The complete
        // typed consumer supplies their domains; matching never invents them.
        for (&root, referent) in [motive, false_minor, true_minor].into_iter().zip([
            Referent::Bool,
            Referent::False,
            Referent::True,
        ]) {
            let ExprKind::Lambda(_, _, body, _) = e.get(root, b)?.kind(e, l, b)? else {
                return Ok(None);
            };
            let body = match e.get(body, b)?.kind(e, l, b)? {
                ExprKind::App(function, argument) if !matches!(referent, Referent::Bool) => {
                    // Exact inlined decide minors have one ignored proof beta.
                    // Its raw argument must be the minor's own bound proof;
                    // no arbitrary computation is skipped or guessed here.
                    if !matches!(e.get(argument, b)?.kind(e, l, b)?, ExprKind::Bound(0)) {
                        return Ok(None);
                    }
                    let ExprKind::Lambda(_, _, body, _) = e.get(function, b)?.kind(e, l, b)? else {
                        return Ok(None);
                    };
                    body
                }
                _ => body,
            };
            let ExprKind::Constant(name, []) = e.get(body, b)?.kind(e, l, b)? else {
                return Ok(None);
            };
            if self.finite_named(name, referent, scope, n, b)?.is_none() {
                return Ok(None);
            }
        }
        let Some((head, family)) = (match transported {
            Some(value) => Some(value),
            None => application3(*instance, e, l, b)?,
        }) else {
            return Ok(None);
        };
        let ExprKind::Constant(name, []) = e.get(head, b)?.kind(e, l, b)? else {
            return Ok(None);
        };
        let finite = if self
            .finite_named(name, Referent::Finite, scope, n, b)?
            .is_some()
        {
            true
        } else if self
            .finite_named(name, Referent::Ball, scope, n, b)?
            .is_some()
        {
            false
        } else {
            return Ok(None);
        };
        for &root in &family {
            if e.get(root, b)?.loose_range() != 0 {
                return Ok(None);
            }
        }
        Ok(Some(Request {
            source,
            consumer: slot,
            operands: [*proposition, family[0], family[1], family[2]],
            finite,
            saved_end: 0,
            saved_depth: 0,
        }))
    }
}
fn application3(
    root: ExprId,
    e: &Expressions,
    l: &Levels,
    b: &mut Budget,
) -> Result<Option<(ExprId, [ExprId; 3])>, ResourceError> {
    let mut arguments = [root; 3];
    let mut at = root;
    for index in (0..3).rev() {
        let ExprKind::App(function, argument) = e.get(at, b)?.kind(e, l, b)? else {
            return Ok(None);
        };
        arguments[index] = argument;
        at = function;
    }
    Ok(Some((at, arguments)))
}
