//! Direct raw schemas; no template substitution or retained handles.
use crate::decode::primitive_decode::quotients::Role;
use crate::resource::{Budget, ResourceError};
use crate::syntax::expressions::{BinderInfo, ExprId, ExprKind, ExpressionError, Expressions};
use crate::syntax::levels::{LevelId, Levels, NameId};
use crate::syntax::names::Names;

struct Builder<'a> {
    expressions: &'a mut Expressions,
    levels: &'a Levels,
    names: &'a Names,
    budget: &'a mut Budget,
}
impl Builder<'_> {
    fn node(&mut self, kind: ExprKind<'_>) -> Result<ExprId, ExpressionError> {
        self.expressions
            .append(kind, self.levels, self.names, self.budget)
    }
    fn app(&mut self, f: ExprId, a: ExprId) -> Result<ExprId, ExpressionError> {
        self.node(ExprKind::App(f, a))
    }
    fn pi(
        &mut self,
        domain: ExprId,
        body: ExprId,
        implicit: bool,
    ) -> Result<ExprId, ExpressionError> {
        self.node(ExprKind::Pi(
            NameId::ANONYMOUS,
            domain,
            body,
            if implicit {
                BinderInfo::Implicit
            } else {
                BinderInfo::Default
            },
        ))
    }
    fn relation(&mut self, b: &[ExprId; 5], prop: ExprId) -> Result<ExprId, ExpressionError> {
        // Under A: (a : A) -> (b : A) -> Prop.
        let body = self.pi(b[1], prop, false)?;
        self.pi(b[0], body, false)
    }
    fn apply2(&mut self, f: ExprId, a: ExprId, b: ExprId) -> Result<ExprId, ExpressionError> {
        let f = self.app(f, a)?;
        self.app(f, b)
    }
    fn bounds(&mut self) -> Result<[ExprId; 5], ExpressionError> {
        Ok([
            self.node(ExprKind::Bound(0))?,
            self.node(ExprKind::Bound(1))?,
            self.node(ExprKind::Bound(2))?,
            self.node(ExprKind::Bound(3))?,
            self.node(ExprKind::Bound(4))?,
        ])
    }
}

/// The caller owns all generated syntax and must abandon the session on error.
/// `arguments` has the exact role arity and is checked in the requesting scope.
/// Every universe occurrence below uses its supplied handle verbatim. Bound
/// nodes are raw relative indices, shared only inside this construction; the
/// context comments specify the binder interpretation at each occurrence.
pub(in crate::check::environment) fn build(
    role: Role,
    names: &[NameId; 7],
    arguments: &[LevelId],
    expressions: &mut Expressions,
    levels: &mut Levels,
    all_names: &Names,
    budget: &mut Budget,
) -> Result<ExprId, ExpressionError> {
    let arity = if role == Role::Lift { 2 } else { 1 };
    if arguments.len() != arity {
        return Err(ResourceError::Invariant.into());
    }
    let u = arguments[0];
    let mut s = Builder {
        expressions,
        levels,
        names: all_names,
        budget,
    };
    let b = s.bounds()?;
    let su = s.node(ExprKind::Sort(u))?;
    let prop = s.node(ExprKind::Sort(LevelId::ZERO))?;
    let relation = s.relation(&b, prop)?;
    let tail = match role {
        Role::Type => s.pi(relation, su, false)?,
        Role::Constructor => {
            let quot = s.node(ExprKind::Constant(names[1], &[u]))?;
            // Under A,r,a: Quot A r. The a domain is under A,r.
            let result = s.apply2(quot, b[2], b[1])?;
            let a = s.pi(b[1], result, false)?;
            s.pi(relation, a, false)?
        }
        Role::Lift => {
            let v = arguments[1];
            let sv = s.node(ExprKind::Sort(v))?;
            let eq = s.node(ExprKind::Constant(names[0], &[v]))?;
            let quot = s.node(ExprKind::Constant(names[1], &[u]))?;
            // Under A,r,B: f : (a : A) -> B.
            let f_type = s.pi(b[2], b[1], false)?;
            // Under A,r,B,f,a,b,h: Eq B (f a) (f b).
            let fa = s.app(b[3], b[2])?;
            let fb = s.app(b[3], b[1])?;
            let eq_b = s.app(eq, b[4])?;
            let eq_fa = s.app(eq_b, fa)?;
            let equality = s.app(eq_fa, fb)?;
            // Under A,r,B,f,a,b: r a b; then bind h,b,a.
            let related = s.apply2(b[4], b[1], b[0])?;
            let h = s.pi(related, equality, false)?;
            let other = s.pi(b[4], h, false)?;
            let respect = s.pi(b[3], other, false)?;
            // Under A,r,B,f,respect: Quot A r; under q, B is index 3.
            let quotient = s.apply2(quot, b[4], b[3])?;
            let q = s.pi(quotient, b[3], false)?;
            let respect = s.pi(respect, q, false)?;
            let f = s.pi(f_type, respect, false)?;
            let target = s.pi(sv, f, true)?;
            s.pi(relation, target, true)?
        }
        Role::Induction => {
            let quot = s.node(ExprKind::Constant(names[1], &[u]))?;
            let mk = s.node(ExprKind::Constant(names[2], &[u]))?;
            // Under A,r: P : Quot A r -> Prop.
            let quotient = s.apply2(quot, b[1], b[0])?;
            let predicate = s.pi(quotient, prop, false)?;
            // Under A,r,P,a: P (Quot.mk A r a).
            let constructor = s.apply2(mk, b[3], b[2])?;
            let constructor = s.app(constructor, b[0])?;
            let instance = s.app(b[1], constructor)?;
            let minor = s.pi(b[2], instance, false)?;
            // Under A,r,P,minor,q: P q.
            let result = s.app(b[2], b[0])?;
            let quotient = s.apply2(quot, b[3], b[2])?;
            let q = s.pi(quotient, result, false)?;
            let minor = s.pi(minor, q, false)?;
            let predicate = s.pi(predicate, minor, true)?;
            s.pi(relation, predicate, true)?
        }
    };
    s.pi(su, tail, true)
}

/// Expected Eq type, using the declaration's actual sole parameter level.
pub(in crate::check::environment) fn eq_type(
    universe: LevelId,
    expressions: &mut Expressions,
    levels: &mut Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<ExprId, ExpressionError> {
    let mut s = Builder {
        expressions,
        levels,
        names,
        budget,
    };
    let b = s.bounds()?;
    let su = s.node(ExprKind::Sort(universe))?;
    let prop = s.node(ExprKind::Sort(LevelId::ZERO))?;
    let relation = s.relation(&b, prop)?;
    s.pi(su, relation, true)
}

/// Expected sole Eq constructor type. Its constant uses the validated Eq name,
/// and exactly the supplied universe handle, never an invented parameter level.
pub(in crate::check::environment) fn eq_constructor(
    eq: NameId,
    universe: LevelId,
    expressions: &mut Expressions,
    levels: &mut Levels,
    names: &Names,
    budget: &mut Budget,
) -> Result<ExprId, ExpressionError> {
    let mut s = Builder {
        expressions,
        levels,
        names,
        budget,
    };
    let b = s.bounds()?;
    let su = s.node(ExprKind::Sort(universe))?;
    let eq = s.node(ExprKind::Constant(eq, &[universe]))?;
    // Under A,a: Eq A a a.
    let result = s.apply2(eq, b[1], b[0])?;
    let result = s.app(result, b[0])?;
    let a = s.pi(b[0], result, false)?;
    s.pi(su, a, true)
}
