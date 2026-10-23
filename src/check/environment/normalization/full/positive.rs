//! Positive syntax baseline inside a fixed-scope session.
//! Both operands must already be checked types in the same validated context.
use super::{Normal, Session, select_failure};
use crate::check::environment::normalization::{HeadError, release};
use crate::resource::{Budget, Event, ReductionPath, ResourceError};
use crate::syntax::expressions::{ExprId, ExprKind};
use crate::syntax::levels::{
    LevelId, LevelKind, LevelNames, Levels, NameId, SharedTable, UniverseComparison,
};
use std::mem::size_of;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Pair {
    Expression(ExprId, ExprId),
    Level(LevelId, LevelId),
}
const _: () = assert!(size_of::<Pair>() == 12);
const _: () = assert!(size_of::<Option<Pair>>() == 12);

mod reuse;
use reuse::Reuse;

fn push(stack: &mut Vec<Pair>, pair: Pair, budget: &mut Budget) -> Result<(), ResourceError> {
    // One fixed-alpha, immutable structural conjunction. An exact queued pair
    // still has to complete before the whole walk succeeds. Raw bound indices
    // do not depend on binder depth here. No result, negative or equivalence
    // closure is cached, and no obligation survives this invocation.
    // Four comparisons are bounded parent-visit work; no extra storage/hash.
    if stack.iter().rev().take(4).any(|pending| *pending == pair) {
        return Ok(());
    }
    let needed = stack.len().checked_add(1).ok_or(ResourceError::Counter)?;
    budget.reserve_frames(1)?;
    if let Err(error) = budget.grow_vec(stack, needed) {
        budget.release_frames(1)?;
        return Err(error);
    }
    stack.push(pair);
    Ok(())
}

/// How one structural walk discharges its level obligations.
pub(crate) enum LevelRule<'a> {
    /// C1 identity of original checked operands: raw level syntax, compared
    /// positionally. Max/IMax child order is significant.
    Identity(&'a Levels),
    /// Full-normal-form comparison: each whole level
    /// obligation -- one Sort level, or one universe-argument position of a
    /// constant -- is discharged by handle identity, by raw structural equality
    /// (tried only when the structural hashes agree), or U on the
    /// enclosing pair. A failed positional child never decides the obligation.
    /// The optional operation-scoped memo retains
    /// completed U results across the owner's U requests; `None` reproduces
    /// the per-request memo discipline exactly.
    Universe(&'a mut Levels, Option<SharedTable<'a>>),
}

// Monomorphic walk per rule: the C1 identity instantiation carries no level
// obligation state, fingerprint bypass or U fallback at run time.
trait Rule {
    const IDENTITY: bool;
    fn levels(&self) -> &Levels;
    fn decide(
        &mut self,
        left: LevelId,
        right: LevelId,
        names: &crate::syntax::names::Names,
        budget: &mut Budget,
    ) -> Result<(), HeadError>;
}
struct Identity<'a>(&'a Levels);
struct Universe<'a>(&'a mut Levels, Option<SharedTable<'a>>);
impl Rule for Identity<'_> {
    const IDENTITY: bool = true;
    fn levels(&self) -> &Levels {
        self.0
    }
    fn decide(
        &mut self,
        _: LevelId,
        _: LevelId,
        _: &crate::syntax::names::Names,
        _: &mut Budget,
    ) -> Result<(), HeadError> {
        // Unreachable: the Identity walk never opens a level obligation.
        Err(ResourceError::Invariant.into())
    }
}
impl Rule for Universe<'_> {
    const IDENTITY: bool = false;
    fn levels(&self) -> &Levels {
        self.0
    }
    fn decide(
        &mut self,
        left: LevelId,
        right: LevelId,
        names: &crate::syntax::names::Names,
        budget: &mut Budget,
    ) -> Result<(), HeadError> {
        universe_obligation(left, right, self.0, self.1.as_mut(), names, budget)
    }
}

impl Session<'_> {
    /// Positive evidence only after both full normalizations and syntax
    /// comparison up to Pi/lambda metadata and U on whole level obligations. Caller supplies incoming paths; this does not decide how
    /// inference composes routes. Same-origin checkedness is a premise, not an
    /// inference from equal handles. Every mismatch is Unsupported/inconclusive.
    pub(crate) fn compare(
        &mut self,
        left: ExprId,
        left_path: ReductionPath,
        right: ExprId,
        right_path: ReductionPath,
    ) -> Result<(Normal, Normal), HeadError> {
        let left = self.normalize(left, left_path)?;
        let right = self.normalize(right, right_path)?;
        self.poisoned = true;
        let result = self.compare_normal(left.expression, right.expression);
        self.poisoned = false;
        if let Err(error) = result {
            self.failure = Some(error);
        }
        result.map(|()| (left, right))
    }

    /// C1 on original terms with checked derivations in this context.
    /// This returns equality evidence only, never a normal-form certificate.
    pub(crate) fn structurally_identical(
        &mut self,
        left: ExprId,
        right: ExprId,
    ) -> Result<bool, HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if self.poisoned {
            return Err(ResourceError::Invariant.into());
        }
        self.poisoned = true;
        let result = self.compare_structure(left, right, true);
        self.poisoned = false;
        match result {
            Ok(()) => Ok(true),
            // No identity evidence. A separate positive route may still succeed.
            Err(HeadError::Unsupported) => Ok(false),
            Err(error) => {
                self.failure = Some(error);
                Err(error)
            }
        }
    }

    fn compare_normal(&mut self, left: ExprId, right: ExprId) -> Result<(), HeadError> {
        self.compare_structure(left, right, false)
    }

    fn compare_structure(
        &mut self,
        left: ExprId,
        right: ExprId,
        alpha: bool,
    ) -> Result<(), HeadError> {
        let rule = if alpha {
            LevelRule::Identity(self.levels)
        } else {
            LevelRule::Universe(self.levels, None)
        };
        compare_structure(left, right, rule, self.expressions, self.names, self.budget)
    }
}

fn same_name(
    names: &crate::syntax::names::Names,
    left: NameId,
    right: NameId,
    budget: &mut Budget,
) -> Result<bool, ResourceError> {
    Ok(names.summary(left, budget)?.canonical == names.summary(right, budget)?.canonical)
}

pub(super) fn compare_structure(
    left: ExprId,
    right: ExprId,
    rule: LevelRule<'_>,
    expressions: &crate::syntax::expressions::Expressions,
    names: &crate::syntax::names::Names,
    budget: &mut Budget,
) -> Result<(), HeadError> {
    match rule {
        LevelRule::Identity(levels) => {
            walk(left, right, Identity(levels), expressions, names, budget)
        }
        LevelRule::Universe(levels, shared) => walk(
            left,
            right,
            Universe(levels, shared),
            expressions,
            names,
            budget,
        ),
    }
}

fn walk<R: Rule>(
    left: ExprId,
    right: ExprId,
    mut rule: R,
    expressions: &crate::syntax::expressions::Expressions,
    names: &crate::syntax::names::Names,
    budget: &mut Budget,
) -> Result<(), HeadError> {
    // Identity is C1 alpha structural identity of original checked operands;
    // Universe compares full normal forms up to Pi/lambda binder metadata
    // and whole-level U; projection names and indices remain significant.
    let alpha = R::IDENTITY;
    // C1 is evidence about original checked operands, not a normal-form
    // certificate. Resolve both kinds before the existing identity authority;
    // fingerprint misses abandon only this route. No scratch survives a call.
    if alpha {
        let prefix = (|| -> Result<bool, HeadError> {
            budget.charge_work(1)?;
            let left_node = expressions.get(left, budget)?;
            left_node.kind(expressions, rule.levels(), budget)?;
            let right_node = expressions.get(right, budget)?;
            right_node.kind(expressions, rule.levels(), budget)?;
            if left == right {
                return Ok(true);
            }
            let filter = true;
            if filter && left_node.syntax_fingerprint() != right_node.syntax_fingerprint() {
                return Err(HeadError::Unsupported);
            }
            Ok(false)
        })();
        if prefix != Ok(false) {
            budget.observe(Event::ConversionSteps, 1);
            budget.observe(Event::MachineSteps, 1);
            let result = prefix.map(|_| ());
            return result;
        }
    }
    budget.charge_work(1)?; // prepay flat scratch release
    let mut stack = Vec::new();
    let mut reuse = Reuse::default();
    // Universe rule only: the level obligation whose raw structural walk is in
    // progress, and the stack length below its children. The walk pushes only
    // level pairs, so every entry above `base` belongs to it (LIFO). `push` may
    // suppress a child that duplicates a pending pair below `base` (another
    // whole obligation). That pair is still decided later, by raw equality or
    // U-Equal, and succ/max/imax preserve equality of interpreted levels, so
    // the enclosing obligation's raw derivation stays valid by congruence.
    let mut obligation: Option<(LevelId, LevelId, usize)> = None;
    let result = (|| {
        push(&mut stack, Pair::Expression(left, right), budget)?;
        loop {
            if obligation.is_some_and(|(_, _, base)| stack.len() <= base) {
                obligation = None;
            }
            let Some(pair) = stack.pop() else {
                break;
            };
            budget.release_frames(1)?;
            budget.charge_work(1)?;
            budget.observe(Event::ConversionSteps, 1);
            budget.observe(Event::MachineSteps, 1);
            match pair {
                Pair::Expression(left, right) => {
                    let left_node = expressions.get(left, budget)?;
                    let a = left_node.kind(expressions, rule.levels(), budget)?;
                    let right_node = expressions.get(right, budget)?;
                    let b = right_node.kind(expressions, rule.levels(), budget)?;
                    // Original checked terms need no normalization for C1.
                    // The old normal-form path retains its shape guard below.
                    if alpha && left == right {
                        continue;
                    }
                    // Let pairs use C1 identity or positive Universe congruence below;
                    // neither establishes normalization. A Let against any other form
                    // has no certificate. Projection pairs
                    // are compared below under both rules; a projection against any
                    // other form falls to the final no-match arm.
                    if matches!(a, ExprKind::Let(..)) != matches!(b, ExprKind::Let(..)) {
                        return Err(HeadError::Unsupported);
                    }
                    if left == right {
                        continue;
                    }
                    // In this immutable, already-checked store, alpha-identical
                    // syntax has the same construction-time fingerprint. A miss
                    // abandons only structural identity; it is not a conversion
                    // negative. Collisions still take the full walk below. Raw
                    // theorem identity and level-handle-sensitive keys do not use
                    // this filter. No obligation/result survives this call.
                    // Fingerprints hash raw level syntax, so under the Universe
                    // rule a miss can be a U-equal level: walk instead.
                    let filter = alpha;
                    if filter && left_node.syntax_fingerprint() != right_node.syntax_fingerprint() {
                        return Err(HeadError::Unsupported);
                    }
                    if alpha
                        && reuse.seen(pair, budget, || match (a, b) {
                            (ExprKind::Bound(_) | ExprKind::Free(_), _) => false,
                            (ExprKind::Constant(_, []), _) => false,
                            (ExprKind::Sort(x), ExprKind::Sort(y)) if x == y => false,
                            _ => true,
                        })?
                    {
                        continue;
                    }
                    match (a, b) {
                        (ExprKind::Bound(a), ExprKind::Bound(b))
                        | (ExprKind::Free(a), ExprKind::Free(b))
                            if a == b => {}
                        (ExprKind::Sort(a), ExprKind::Sort(b)) => {
                            push(&mut stack, Pair::Level(a, b), budget)?;
                        }
                        // Syntactic identity only: same canonical structure name and
                        // field index (both are in the fingerprint), then the targets.
                        // No projection or iota step is taken.
                        (ExprKind::Projection(an, ai, av), ExprKind::Projection(bn, bi, bv))
                            if ai == bi && same_name(names, an, bn, budget)? =>
                        {
                            push(&mut stack, Pair::Expression(av, bv), budget)?;
                        }
                        // Checked lets bind by de Bruijn position, not display name.
                        // C1 retains the nondependent flag in its fingerprint contract;
                        // Universe congruence also ignores that hint. Both routes
                        // require every type, value and body obligation to complete.
                        (
                            ExprKind::Let(_, at, av, ab, a_nondep),
                            ExprKind::Let(_, bt, bv, bb, b_nondep),
                        ) if !alpha || a_nondep == b_nondep => {
                            push(&mut stack, Pair::Expression(ab, bb), budget)?;
                            push(&mut stack, Pair::Expression(av, bv), budget)?;
                            push(&mut stack, Pair::Expression(at, bt), budget)?;
                        }
                        (ExprKind::App(af, aa), ExprKind::App(bf, ba)) => {
                            push(&mut stack, Pair::Expression(aa, ba), budget)?;
                            push(&mut stack, Pair::Expression(af, bf), budget)?;
                        }
                        // In one validated context, de Bruijn bodies bind by position.
                        // Pi/lambda names and BinderInfo carry no conversion premise;
                        // both domain and body obligations must still complete.
                        (ExprKind::Pi(_, ad, ab, _), ExprKind::Pi(_, bd, bb, _))
                        | (ExprKind::Lambda(_, ad, ab, _), ExprKind::Lambda(_, bd, bb, _)) => {
                            push(&mut stack, Pair::Expression(ab, bb), budget)?;
                            push(&mut stack, Pair::Expression(ad, bd), budget)?;
                        }
                        (ExprKind::Constant(an, aa), ExprKind::Constant(bn, ba))
                            if aa.len() == ba.len() && same_name(names, an, bn, budget)? =>
                        {
                            budget.charge_work(aa.len() as u64)?;
                            for (&a, &b) in aa.iter().zip(ba).rev() {
                                push(&mut stack, Pair::Level(a, b), budget)?;
                            }
                        }
                        (ExprKind::Natural(a), ExprKind::Natural(b))
                        | (ExprKind::String(a), ExprKind::String(b))
                            if a.len() == b.len() =>
                        {
                            budget.charge_work(a.len() as u64)?;
                            if a != b {
                                return Err(HeadError::Unsupported);
                            }
                        }
                        _ => return Err(HeadError::Unsupported),
                    }
                }
                Pair::Level(left, right) => {
                    let x = rule.levels().get(left, budget)?;
                    let y = rule.levels().get(right, budget)?;
                    let (a, b) = (x.kind(), y.kind());
                    if left == right {
                        // One handle is one immutable node of this declaration's
                        // level store: the same interpreted level on both sides.
                        continue;
                    }
                    if alpha
                        && reuse.seen(pair, budget, || {
                            !matches!(a, LevelKind::Zero | LevelKind::Param(_))
                        })?
                    {
                        continue;
                    }
                    let mut whole = None;
                    if !R::IDENTITY && obligation.is_none() {
                        // A new whole obligation. Equal raw syntax implies equal
                        // hashes, so a hash miss goes straight to U.
                        if x.structural_hash() == y.structural_hash() {
                            obligation = Some((left, right, stack.len()));
                        } else {
                            whole = Some((left, right));
                        }
                    }
                    if whole.is_none() {
                        let matched = match (a, b) {
                            (LevelKind::Zero, LevelKind::Zero) => true,
                            (LevelKind::Succ(a), LevelKind::Succ(b)) => {
                                push(&mut stack, Pair::Level(a, b), budget)?;
                                true
                            }
                            (LevelKind::Max(al, ar), LevelKind::Max(bl, br))
                            | (LevelKind::IMax(al, ar), LevelKind::IMax(bl, br)) => {
                                push(&mut stack, Pair::Level(ar, br), budget)?;
                                push(&mut stack, Pair::Level(al, bl), budget)?;
                                true
                            }
                            (LevelKind::Param(a), LevelKind::Param(b)) => {
                                same_name(names, a, b, budget)?
                            }
                            _ => false,
                        };
                        if matched {
                            continue;
                        }
                        // Identity rule: raw syntax differs. Universe rule: the
                        // raw walk failed somewhere inside this obligation;
                        // discard its pending children and decide the enclosing
                        // pair instead of the mismatched child.
                        let Some((left, right, base)) = obligation.take() else {
                            return Err(HeadError::Unsupported);
                        };
                        let count = stack.len() - base;
                        stack.truncate(base);
                        budget.release_frames(count)?;
                        whole = Some((left, right));
                    }
                    let Some((left, right)) = whole else {
                        return Err(ResourceError::Invariant.into());
                    };
                    rule.decide(left, right, names, budget)?;
                }
            }
        }
        Ok(())
    })();
    let count = stack.len();
    let storage = release(stack, budget);
    let frames = budget.release_frames(count);
    let table = reuse.retire(budget);
    let error = select_failure([
        result.as_ref().err().copied(),
        storage.err().map(HeadError::from),
        frames.err().map(HeadError::from),
        table.err().map(HeadError::from),
    ]);
    match error {
        Some(error) => Err(error),
        None => result,
    }
}

/// The enclosing level obligation, decided unchanged U. Rare
/// (the raw walk decides almost every obligation), so kept out of line.
/// Invariant (by construction): both handles are levels of checked operands or
/// of their normal forms, generated only substitution into this
/// declaration's validated universe scope, so U's scope premise holds. Equal
/// discharges only this obligation; the caller's remaining pairs still run.
/// NotEqual is an algorithmic result, not a negative: inconclusive here.
/// Resource and invariant failures keep their categories.
#[cold]
#[inline(never)]
fn universe_obligation(
    left: LevelId,
    right: LevelId,
    levels: &mut Levels,
    shared: Option<&mut SharedTable<'_>>,
    names: &crate::syntax::names::Names,
    budget: &mut Budget,
) -> Result<(), HeadError> {
    match levels.with_helpers(names, budget, |helpers| {
        helpers.compare_universes_with(
            left,
            right,
            shared.map(|table| SharedTable {
                memo: table.memo,
                ledger: table.ledger,
            }),
        )
    })? {
        UniverseComparison::Equal => Ok(()),
        UniverseComparison::NotEqual => Err(HeadError::Unsupported),
    }
}
