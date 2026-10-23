//! The ordered sufficient universe-domination procedure.
//! Every subcall normalizes both operands afresh. No D result is cached, and
//! false is a completed admission-algorithm result, not numerical inequality.
use super::{Helpers, Map, Normalizer, release_vec};
use crate::resource::{Budget, Event, ResourceError, failure::FailureOutcome};
use crate::syntax::levels::{LevelId, LevelKind, OrderedLevelNames};

#[derive(Clone, Copy)]
enum Frame {
    Visit(LevelId, LevelId),
    And(LevelId, LevelId),
    Or {
        left: LevelId,
        right: LevelId,
        second: LevelId,
    },
    OrDone(LevelId, LevelId),
    Tail(LevelId, LevelId),
}
const _: () = assert!(std::mem::size_of::<Frame>() <= 16);
fn push(stack: &mut Vec<Frame>, frame: Frame, b: &mut Budget) -> Result<(), ResourceError> {
    let n = stack.len().checked_add(1).ok_or(ResourceError::Counter)?;
    b.reserve_frames(1)?;
    if let Err(e) = b.grow_vec(stack, n) {
        b.release_frames(1)?;
        return Err(e);
    }
    stack.push(frame);
    Ok(())
}
fn selected(errors: impl IntoIterator<Item = Option<ResourceError>>) -> Option<ResourceError> {
    let mut first = None;
    for error in errors.into_iter().flatten() {
        if error.failure_report().outcome == FailureOutcome::InternalError {
            return Some(error);
        }
        if first.is_none() {
            first = Some(error)
        }
    }
    first
}
impl<N: OrderedLevelNames> Helpers<'_, N> {
    /// Requires valid levels and declaration universe scope. Each subcall runs
    /// one-pass N on left then right, including generated operands from its
    /// parent. N's completed memo exists only for that frozen pair invocation;
    /// reusing it across D subcalls would incorrectly assume N idempotent.
    pub(crate) fn dominates(
        &mut self,
        left: LevelId,
        right: LevelId,
    ) -> Result<bool, ResourceError> {
        self.attempt(|h| h.domination_inner(left, right))
    }
    fn normalize_domination_pair(
        &mut self,
        left: LevelId,
        right: LevelId,
    ) -> Result<(LevelId, LevelId), ResourceError> {
        self.budget.charge_work(5)?;
        let source_end = self.levels.len();
        let mut n = Normalizer {
            h: self,
            source_end,
            memo: Map::default(),
            shared: None,
            frames: Vec::new(),
            results: Vec::new(),
            frontier: Vec::new(),
            scan: Vec::new(),
        };
        let result = (|| {
            let left = n.normalize(left)?;
            let right = n.normalize(right)?;
            Ok((left, right))
        })();
        let remaining = n
            .frames
            .len()
            .checked_add(n.results.len())
            .and_then(|x| x.checked_add(n.scan.len()));
        let errors = [
            result.as_ref().err().copied(),
            remaining
                .ok_or(ResourceError::Counter)
                .and_then(|count| n.h.budget.release_frames(count))
                .err(),
            release_vec(n.frames, n.h.budget).err(),
            release_vec(n.results, n.h.budget).err(),
            release_vec(n.frontier, n.h.budget).err(),
            release_vec(n.scan, n.h.budget).err(),
            release_vec(n.memo.entries, n.h.budget).err(),
        ];
        match selected(errors) {
            Some(error) => Err(error),
            None => result,
        }
    }
    fn domination_inner(&mut self, left: LevelId, right: LevelId) -> Result<bool, ResourceError> {
        self.budget.charge_work(1)?; // prepay the D continuation vector retirement
        let mut stack = Vec::new();
        let mut value = None;
        let result = (|| {
            push(&mut stack, Frame::Visit(left, right), self.budget)?;
            while let Some(frame) = stack.pop() {
                self.budget.release_frames(1)?;
                self.budget.charge_work(1)?;
                self.budget.observe(Event::MachineSteps, 1);
                match frame {
                    Frame::Visit(a, b) => {
                        if value.is_some() {
                            return Err(ResourceError::Invariant);
                        }
                        let (a, b) = self.normalize_domination_pair(a, b)?;
                        if self.structural(a, b)?
                            || matches!(self.levels.get(b, self.budget)?.kind(), LevelKind::Zero)
                        {
                            value = Some(true);
                        } else if let LevelKind::Max(x, y) = self.levels.get(b, self.budget)?.kind()
                        {
                            push(&mut stack, Frame::And(a, y), self.budget)?;
                            push(&mut stack, Frame::Visit(a, x), self.budget)?;
                        } else if let LevelKind::Max(x, y) = self.levels.get(a, self.budget)?.kind()
                        {
                            push(
                                &mut stack,
                                Frame::Or {
                                    left: a,
                                    right: b,
                                    second: y,
                                },
                                self.budget,
                            )?;
                            push(&mut stack, Frame::Visit(x, b), self.budget)?;
                        } else {
                            push(&mut stack, Frame::Tail(a, b), self.budget)?;
                        }
                    }
                    Frame::And(a, b) => {
                        if value.take().ok_or(ResourceError::Invariant)? {
                            push(&mut stack, Frame::Visit(a, b), self.budget)?;
                        } else {
                            value = Some(false);
                        }
                    }
                    Frame::Or {
                        left,
                        right,
                        second,
                    } => {
                        if value.take().ok_or(ResourceError::Invariant)? {
                            value = Some(true);
                        } else {
                            push(&mut stack, Frame::OrDone(left, right), self.budget)?;
                            push(&mut stack, Frame::Visit(second, right), self.budget)?;
                        }
                    }
                    Frame::OrDone(a, b) => {
                        if value.take().ok_or(ResourceError::Invariant)? {
                            value = Some(true);
                        } else {
                            push(&mut stack, Frame::Tail(a, b), self.budget)?;
                        }
                    }
                    Frame::Tail(a, b) => {
                        if value.is_some() {
                            return Err(ResourceError::Invariant);
                        }
                        // Ordered fallthrough after both left-Max alternatives
                        // failed. Do not renormalize this same parent here.
                        if let LevelKind::IMax(x, y) = self.levels.get(b, self.budget)?.kind() {
                            push(&mut stack, Frame::And(a, y), self.budget)?;
                            push(&mut stack, Frame::Visit(a, x), self.budget)?;
                        } else if let LevelKind::IMax(_, y) =
                            self.levels.get(a, self.budget)?.kind()
                        {
                            push(&mut stack, Frame::Visit(y, b), self.budget)?;
                        } else {
                            let (a, ak) = self.offset(a)?;
                            let (b, bk) = self.offset(b)?;
                            if self.structural(a, b)?
                                || matches!(
                                    self.levels.get(b, self.budget)?.kind(),
                                    LevelKind::Zero
                                )
                            {
                                value = Some(ak >= bk);
                            } else if ak == bk && ak > 0 {
                                push(&mut stack, Frame::Visit(a, b), self.budget)?;
                            } else {
                                value = Some(false);
                            }
                        }
                    }
                }
            }
            value.ok_or(ResourceError::Invariant)
        })();
        let remaining = stack.len();
        let errors = [
            result.as_ref().err().copied(),
            release_vec(stack, self.budget).err(),
            self.budget.release_frames(remaining).err(),
        ];
        match selected(errors) {
            Some(error) => Err(error),
            None => result,
        }
    }
}
