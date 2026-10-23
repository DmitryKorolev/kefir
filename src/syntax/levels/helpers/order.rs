//! Frontier ordering. It is exact syntax order, not universe equality.
use super::{Helpers, release_vec};
use crate::resource::{Budget, ResourceError};
use crate::syntax::levels::{LevelId, LevelKind, OrderedLevelNames};
use std::cmp::Ordering;

#[derive(Clone, Copy)]
enum Frame {
    Nodes(LevelId, LevelId),
    Offsets(u32, u32),
}
const _: () = assert!(std::mem::size_of::<Frame>() <= 12);

fn push(stack: &mut Vec<Frame>, f: Frame, b: &mut Budget) -> Result<(), ResourceError> {
    let len = stack.len().checked_add(1).ok_or(ResourceError::Counter)?;
    b.reserve_frames(1)?;
    if let Err(e) = b.grow_vec(stack, len) {
        b.release_frames(1)?;
        return Err(e);
    }
    stack.push(f);
    Ok(())
}

fn rank(k: LevelKind) -> Result<u8, ResourceError> {
    Ok(match k {
        LevelKind::Zero => 0,
        LevelKind::Max(..) => 1,
        LevelKind::IMax(..) => 2,
        LevelKind::Param(_) => 3,
        LevelKind::Succ(_) => return Err(ResourceError::Invariant),
    })
}

impl<N: OrderedLevelNames> Helpers<'_, N> {
    pub(crate) fn order(&mut self, a: LevelId, c: LevelId) -> Result<Ordering, ResourceError> {
        self.attempt(|h| h.order_inner(a, c))
    }

    fn order_inner(&mut self, a: LevelId, c: LevelId) -> Result<Ordering, ResourceError> {
        self.budget.charge_work(1)?; // reserve the flat stack's eventual release
        let mut stack = Vec::new();
        let result = (|| {
            push(&mut stack, Frame::Nodes(a, c), self.budget)?;
            while let Some(frame) = stack.pop() {
                self.budget.release_frames(1)?;
                self.budget.charge_work(1)?;
                self.budget.observe(crate::resource::Event::MachineSteps, 1);
                let order = match frame {
                    Frame::Offsets(x, y) => x.cmp(&y),
                    Frame::Nodes(a, c) => {
                        let (base_a, offset_a) = self.offset(a)?;
                        let (base_c, offset_c) = self.offset(c)?;
                        if self.structural(base_a, base_c)? {
                            offset_a.cmp(&offset_c)
                        } else {
                            let (x, y) = (
                                self.levels.get(base_a, self.budget)?.kind(),
                                self.levels.get(base_c, self.budget)?.kind(),
                            );
                            let kind = rank(x)?.cmp(&rank(y)?);
                            if kind != Ordering::Equal {
                                return Ok(kind);
                            }
                            match (x, y) {
                                (LevelKind::Param(x), LevelKind::Param(y)) => {
                                    let order = self.names.compare_names(x, y, self.budget)?;
                                    if order == Ordering::Equal {
                                        return Err(ResourceError::Invariant);
                                    }
                                    order
                                }
                                (LevelKind::Max(a1, a2), LevelKind::Max(c1, c2))
                                | (LevelKind::IMax(a1, a2), LevelKind::IMax(c1, c2)) => {
                                    // Lexicographic children before outer offsets.
                                    // Exact structural equality skips equal DAGs;
                                    // this stack never follows native recursion.
                                    push(
                                        &mut stack,
                                        Frame::Offsets(offset_a, offset_c),
                                        self.budget,
                                    )?;
                                    push(&mut stack, Frame::Nodes(a2, c2), self.budget)?;
                                    push(&mut stack, Frame::Nodes(a1, c1), self.budget)?;
                                    Ordering::Equal
                                }
                                _ => return Err(ResourceError::Invariant),
                            }
                        }
                    }
                };
                if order != Ordering::Equal {
                    return Ok(order);
                }
            }
            Ok(Ordering::Equal)
        })();
        let frames = stack.len();
        release_vec(stack, self.budget)?;
        self.budget.release_frames(frames)?;
        result
    }
}
