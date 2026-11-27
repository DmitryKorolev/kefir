//! Exact generated/export schema relation; not conversion or a type judgment.
use crate::decode::primitive_decode::ordinary_session::{Stop, Working};
use crate::resource::{Budget, Event, ResourceError};
use crate::syntax::expressions::{ExprId, ExprKind};
use crate::syntax::levels::{LevelId, LevelKind, LevelNames, NameId};
use crate::syntax::names::Names;
mod memo;
use memo::{Key, Memo};
fn same(names: &Names, a: NameId, b: NameId, bgt: &mut Budget) -> Result<bool, ResourceError> {
    Ok(names.summary(a, bgt)?.canonical == names.summary(b, bgt)?.canonical)
}
// General exact generated/export relation, including raw universe structure.
#[derive(Clone, Copy)]
enum Pair {
    Expression(ExprId, ExprId),
    Level(LevelId, LevelId),
}
pub(super) fn matches(work: &mut Working<'_>, a: ExprId, b: ExprId) -> Result<bool, Stop> {
    compare::<false>(work, a, b)
}

/// Raw identity for specialization keys includes the exact metadata payload.
/// Schema matching retains its own eligibility rule for metadata.
pub(super) fn nested_key(work: &mut Working<'_>, a: ExprId, b: ExprId) -> Result<bool, Stop> {
    compare::<true>(work, a, b)
}

fn compare<const KEY: bool>(work: &mut Working<'_>, a: ExprId, b: ExprId) -> Result<bool, Stop> {
    let mut pairs = Vec::new();
    let mut memo = Memo::default();
    work.budget.reserve(96)?;
    fn pair(
        work: &mut Working<'_>,
        v: &mut Vec<(Pair, bool)>,
        p: Pair,
        finish: bool,
    ) -> Result<(), Stop> {
        let n = v.len().checked_add(1).ok_or(ResourceError::Counter)?;
        work.budget.reserve_frames(1)?;
        if let Err(e) = work.budget.grow_vec(v, n) {
            work.budget.release_frames(1)?;
            return Err(e.into());
        }
        v.push((p, finish));
        Ok(())
    }
    let result = (|| {
        pair(work, &mut pairs, Pair::Expression(a, b), false)?;
        while let Some((p, finish)) = pairs.pop() {
            work.budget.release_frames(1)?;
            work.budget.charge_work(1)?;
            work.budget.observe(Event::MachineSteps, 1);
            let key = Key::from(p);
            if finish {
                memo.insert(key, work.budget)?;
                continue;
            }
            if memo.contains(key, work.budget)? {
                continue;
            }
            // LIFO Finish follows every successfully checked ordered child.
            // Any false/Stop exits before pending parents can enter the memo.
            pair(work, &mut pairs, p, true)?;
            match p {
                Pair::Level(a, b) => match (
                    work.levels.get(a, work.budget)?.kind(),
                    work.levels.get(b, work.budget)?.kind(),
                ) {
                    (LevelKind::Zero, LevelKind::Zero) => (),
                    (LevelKind::Param(a), LevelKind::Param(b)) => {
                        if !same(work.names, a, b, work.budget)? {
                            return Ok(false);
                        }
                    }
                    (LevelKind::Succ(a), LevelKind::Succ(b)) => {
                        pair(work, &mut pairs, Pair::Level(a, b), false)?
                    }
                    (LevelKind::Max(a, c), LevelKind::Max(b, d))
                    | (LevelKind::IMax(a, c), LevelKind::IMax(b, d)) => {
                        pair(work, &mut pairs, Pair::Level(c, d), false)?;
                        pair(work, &mut pairs, Pair::Level(a, b), false)?;
                    }
                    _ => return Ok(false),
                },
                Pair::Expression(a, b) => {
                    let a = work.expressions.get(a, work.budget)?.kind(
                        work.expressions,
                        work.levels,
                        work.budget,
                    )?;
                    let b = work.expressions.get(b, work.budget)?.kind(
                        work.expressions,
                        work.levels,
                        work.budget,
                    )?;
                    match (a, b) {
                        (ExprKind::Pi(_, a, c, _), ExprKind::Pi(_, b, d, _))
                        | (ExprKind::Lambda(_, a, c, _), ExprKind::Lambda(_, b, d, _))
                        | (ExprKind::App(a, c), ExprKind::App(b, d)) => {
                            pair(work, &mut pairs, Pair::Expression(c, d), false)?;
                            pair(work, &mut pairs, Pair::Expression(a, b), false)?;
                        }
                        (ExprKind::Let(_, a, c, e, x), ExprKind::Let(_, b, d, f, y)) if x == y => {
                            pair(work, &mut pairs, Pair::Expression(e, f), false)?;
                            pair(work, &mut pairs, Pair::Expression(c, d), false)?;
                            pair(work, &mut pairs, Pair::Expression(a, b), false)?;
                        }
                        (ExprKind::Bound(a), ExprKind::Bound(b))
                        | (ExprKind::Free(a), ExprKind::Free(b))
                            if a == b => {}
                        (ExprKind::Sort(a), ExprKind::Sort(b)) => {
                            pair(work, &mut pairs, Pair::Level(a, b), false)?
                        }
                        (ExprKind::Constant(a, av), ExprKind::Constant(b, bv)) => {
                            if av.len() != bv.len() || !same(work.names, a, b, work.budget)? {
                                return Ok(false);
                            };
                            // Copy one pair at a time without borrowing the whole Working.
                            for i in 0..av.len() {
                                work.budget.reserve_frames(1)?;
                                let needed =
                                    pairs.len().checked_add(1).ok_or(ResourceError::Counter)?;
                                if let Err(e) = work.budget.grow_vec(&mut pairs, needed) {
                                    work.budget.release_frames(1)?;
                                    return Err(e.into());
                                }
                                pairs.push((Pair::Level(av[i], bv[i]), false));
                            }
                        }
                        (ExprKind::Natural(a), ExprKind::Natural(b))
                        | (ExprKind::String(a), ExprKind::String(b)) => {
                            work.budget.charge_work(a.len() as u64 + 1)?;
                            if a != b {
                                return Ok(false);
                            }
                        }
                        (ExprKind::MData(a, c), ExprKind::MData(b, d)) if KEY => {
                            work.budget.charge_work(a.len() as u64 + 1)?;
                            if a != b {
                                return Ok(false);
                            }
                            pair(work, &mut pairs, Pair::Expression(c, d), false)?;
                        }
                        (ExprKind::Projection(a, i, c), ExprKind::Projection(b, j, d))
                            if i == j =>
                        {
                            if !same(work.names, a, b, work.budget)? {
                                return Ok(false);
                            };
                            pair(work, &mut pairs, Pair::Expression(c, d), false)?;
                        }
                        _ => return Ok(false),
                    }
                }
            }
        }
        Ok(true)
    })();
    let n = pairs.len();
    let bytes = pairs.capacity() * crate::resource::charged::bytes::<(Pair, bool)>();
    drop(pairs);
    let frames = work.budget.release_frames(n);
    let storage = work.budget.release(bytes as u64);
    let memo_storage = memo.retire(work.budget);
    let inline_storage = work.budget.release(96);
    frames?;
    storage?;
    memo_storage?;
    inline_storage?;
    result
}

// Charged sizes (64-bit layout) of this module's stored types.
crate::resource::charged::charged! {
    Pair => 12,
    (Pair, bool) => 16,
    Key => 12,
}
