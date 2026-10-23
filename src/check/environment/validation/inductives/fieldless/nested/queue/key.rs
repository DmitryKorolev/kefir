//! Exact internal key bytes, not a public format. Binder display information is
//! omitted; all semantic scalars and raw level structure are retained. Hashes
//! only filter candidates: byte equality is required. No conversion relation.
use super::*;
use crate::syntax::levels::LevelKind;
#[derive(Clone, Copy)]
enum Visit {
    Expression(ExprId),
    Level(LevelId),
}
fn bytes(out: &mut Vec<u8>, data: &[u8], b: &mut Budget) -> Result<(), Stop> {
    b.charge_work(data.len() as u64 + 1)?;
    let n = out
        .len()
        .checked_add(data.len())
        .ok_or(ResourceError::Counter)?;
    b.grow_vec(out, n)?;
    out.extend_from_slice(data);
    Ok(())
}
fn word(out: &mut Vec<u8>, x: u32, b: &mut Budget) -> Result<(), Stop> {
    bytes(out, &x.to_le_bytes(), b)
}
pub(super) fn encode(root: ExprId, out: &mut Vec<u8>, work: &mut Working<'_>) -> Result<(), Stop> {
    let mut stack = Vec::new();
    let result = (|| {
        push_frame(&mut stack, Visit::Expression(root), work.budget)?;
        while let Some(item) = pop_frame(&mut stack, work.budget)? {
            match item {
                Visit::Level(id) => match work.levels.get(id, work.budget)?.kind() {
                    LevelKind::Zero => word(out, 20, work.budget)?,
                    LevelKind::Succ(a) => {
                        word(out, 21, work.budget)?;
                        push_frame(&mut stack, Visit::Level(a), work.budget)?;
                    }
                    LevelKind::Max(a, b) | LevelKind::IMax(a, b) => {
                        let tag = if matches!(
                            work.levels.get(id, work.budget)?.kind(),
                            LevelKind::Max(..)
                        ) {
                            22
                        } else {
                            23
                        };
                        word(out, tag, work.budget)?;
                        push_frame(&mut stack, Visit::Level(b), work.budget)?;
                        push_frame(&mut stack, Visit::Level(a), work.budget)?;
                    }
                    LevelKind::Param(n) => {
                        word(out, 24, work.budget)?;
                        word(
                            out,
                            work.names.summary(n, work.budget)?.canonical,
                            work.budget,
                        )?;
                    }
                },
                Visit::Expression(id) => {
                    match work.expressions.get(id, work.budget)?.kind(
                        work.expressions,
                        work.levels,
                        work.budget,
                    )? {
                        ExprKind::Bound(i) => {
                            word(out, 0, work.budget)?;
                            word(out, i, work.budget)?;
                        }
                        ExprKind::Free(i) => {
                            word(out, 1, work.budget)?;
                            word(out, i, work.budget)?;
                        }
                        ExprKind::Sort(l) => {
                            word(out, 2, work.budget)?;
                            push_frame(&mut stack, Visit::Level(l), work.budget)?;
                        }
                        ExprKind::App(a, b) => {
                            word(out, 3, work.budget)?;
                            push_frame(&mut stack, Visit::Expression(b), work.budget)?;
                            push_frame(&mut stack, Visit::Expression(a), work.budget)?;
                        }
                        ExprKind::Pi(_, a, b, _) | ExprKind::Lambda(_, a, b, _) => {
                            let tag = if matches!(
                                work.expressions.get(id, work.budget)?.kind(
                                    work.expressions,
                                    work.levels,
                                    work.budget
                                )?,
                                ExprKind::Pi(..)
                            ) {
                                4
                            } else {
                                5
                            };
                            word(out, tag, work.budget)?;
                            push_frame(&mut stack, Visit::Expression(b), work.budget)?;
                            push_frame(&mut stack, Visit::Expression(a), work.budget)?;
                        }
                        ExprKind::Constant(n, ls) => {
                            word(out, 6, work.budget)?;
                            word(
                                out,
                                work.names.summary(n, work.budget)?.canonical,
                                work.budget,
                            )?;
                            word(
                                out,
                                u32::try_from(ls.len()).map_err(|_| ResourceError::Counter)?,
                                work.budget,
                            )?;
                            for &l in ls.iter().rev() {
                                push_frame(&mut stack, Visit::Level(l), work.budget)?;
                            }
                        }
                        ExprKind::Projection(n, i, a) => {
                            word(out, 7, work.budget)?;
                            word(
                                out,
                                work.names.summary(n, work.budget)?.canonical,
                                work.budget,
                            )?;
                            word(out, i, work.budget)?;
                            push_frame(&mut stack, Visit::Expression(a), work.budget)?;
                        }
                        ExprKind::Let(_, a, b, c, nd) => {
                            word(out, 8, work.budget)?;
                            word(out, u32::from(nd), work.budget)?;
                            for e in [c, b, a] {
                                push_frame(&mut stack, Visit::Expression(e), work.budget)?;
                            }
                        }
                        ExprKind::Natural(s) | ExprKind::String(s) => {
                            let tag = if matches!(
                                work.expressions.get(id, work.budget)?.kind(
                                    work.expressions,
                                    work.levels,
                                    work.budget
                                )?,
                                ExprKind::Natural(_)
                            ) {
                                9
                            } else {
                                10
                            };
                            word(out, tag, work.budget)?;
                            word(
                                out,
                                u32::try_from(s.len()).map_err(|_| ResourceError::Counter)?,
                                work.budget,
                            )?;
                            bytes(out, s, work.budget)?;
                        }
                        ExprKind::MData(s, a) => {
                            // Distinct payloads wrap distinct keys; identical
                            // payloads collapse exactly like the store's own
                            // fingerprint identity does.
                            word(out, 11, work.budget)?;
                            word(
                                out,
                                u32::try_from(s.len()).map_err(|_| ResourceError::Counter)?,
                                work.budget,
                            )?;
                            bytes(out, s, work.budget)?;
                            push_frame(&mut stack, Visit::Expression(a), work.budget)?;
                        }
                    }
                }
            }
        }
        Ok(())
    })();
    release_stack(stack, work.budget)?;
    result
}
