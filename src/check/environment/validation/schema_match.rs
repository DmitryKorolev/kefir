//! Exact generated/export schema relation; not conversion or a type judgment.
use crate::decode::primitive_decode::ordinary_session::{Stop, Working};
use crate::resource::{Budget, Event, ResourceError};
use crate::syntax::expressions::{ExprId, ExprKind};
use crate::syntax::levels::{LevelId, LevelKind, LevelNames, NameId};
use crate::syntax::names::Names;
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
    let mut pairs = Vec::new();
    fn pair(work: &mut Working<'_>, v: &mut Vec<Pair>, p: Pair) -> Result<(), Stop> {
        let n = v.len().checked_add(1).ok_or(ResourceError::Counter)?;
        work.budget.reserve_frames(1)?;
        if let Err(e) = work.budget.grow_vec(v, n) {
            work.budget.release_frames(1)?;
            return Err(e.into());
        }
        v.push(p);
        Ok(())
    }
    let result = (|| {
        pair(work, &mut pairs, Pair::Expression(a, b))?;
        while let Some(p) = pairs.pop() {
            work.budget.release_frames(1)?;
            work.budget.charge_work(1)?;
            work.budget.observe(Event::MachineSteps, 1);
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
                        pair(work, &mut pairs, Pair::Level(a, b))?
                    }
                    (LevelKind::Max(a, c), LevelKind::Max(b, d))
                    | (LevelKind::IMax(a, c), LevelKind::IMax(b, d)) => {
                        pair(work, &mut pairs, Pair::Level(c, d))?;
                        pair(work, &mut pairs, Pair::Level(a, b))?;
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
                            pair(work, &mut pairs, Pair::Expression(c, d))?;
                            pair(work, &mut pairs, Pair::Expression(a, b))?;
                        }
                        (ExprKind::Let(_, a, c, e, x), ExprKind::Let(_, b, d, f, y)) if x == y => {
                            pair(work, &mut pairs, Pair::Expression(e, f))?;
                            pair(work, &mut pairs, Pair::Expression(c, d))?;
                            pair(work, &mut pairs, Pair::Expression(a, b))?;
                        }
                        (ExprKind::Bound(a), ExprKind::Bound(b))
                        | (ExprKind::Free(a), ExprKind::Free(b))
                            if a == b => {}
                        (ExprKind::Sort(a), ExprKind::Sort(b)) => {
                            pair(work, &mut pairs, Pair::Level(a, b))?
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
                                pairs.push(Pair::Level(av[i], bv[i]));
                            }
                        }
                        (ExprKind::Natural(a), ExprKind::Natural(b))
                        | (ExprKind::String(a), ExprKind::String(b)) => {
                            work.budget.charge_work(a.len() as u64 + 1)?;
                            if a != b {
                                return Ok(false);
                            }
                        }
                        (ExprKind::Projection(a, i, c), ExprKind::Projection(b, j, d))
                            if i == j =>
                        {
                            if !same(work.names, a, b, work.budget)? {
                                return Ok(false);
                            };
                            pair(work, &mut pairs, Pair::Expression(c, d))?;
                        }
                        _ => return Ok(false),
                    }
                }
            }
        }
        Ok(true)
    })();
    let n = pairs.len();
    let bytes = pairs.capacity() * std::mem::size_of::<Pair>();
    drop(pairs);
    let frames = work.budget.release_frames(n);
    let storage = work.budget.release(bytes as u64);
    frames?;
    storage?;
    result
}
