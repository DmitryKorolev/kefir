//! C7's source delta continuation. No source classification is an outer verdict.
//! Actual child C is requested only by the same-definition or matching-binder
//! rules; a Q miss never schedules full C before paired delta is exhausted.
use super::*;
use crate::check::environment::normalization::Exposure;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Select,
    Arguments,
    ArgumentReply,
    ProbeLeft,
    ProbeRight,
    Unfold,
    Left,
    Right,
    Quick,
    BinderReply,
    Equal,
    Stopped,
}

pub(super) struct State {
    phase: Phase,
    selected: u8,
    incoming: ReductionPath,
    maximum: ReductionPath,
}

pub(in super::super) enum Step {
    Head {
        root: ExprId,
        incoming: ReductionPath,
        exposure: Exposure,
    },
    Comparison {
        left: ExprId,
        right: ExprId,
        incoming: ReductionPath,
    },
    Equal(ReductionPath),
    Stopped,
}

impl Attempt {
    pub(super) fn new(left: ExprId, right: ExprId, incoming: ReductionPath) -> Self {
        Self {
            left: Head {
                expression: left,
                path: incoming,
            },
            right: Head {
                expression: right,
                path: incoming,
            },
            paired: State {
                phase: Phase::Select,
                selected: 0,
                incoming,
                maximum: incoming,
            },
        }
    }

    pub(in super::super) fn incoming(&self) -> ReductionPath {
        self.paired.incoming
    }

    /// Only a genuinely pending optional comparison is an error-recovery
    /// boundary. Required source delta/head operations are not optional children.
    pub(in super::super) fn comparing(&self) -> bool {
        matches!(self.paired.phase, Phase::ArgumentReply | Phase::BinderReply)
    }

    /// The driver has retired an unsupported optional argument and restored its
    /// entry context. Keep actual source reductions, discarding only the failed
    /// shortcut's height. The enclosing owner must become positive-only before
    /// resuming this continuation; no failure here establishes inequality.
    pub(in super::super) fn resume_inconclusive_argument(&mut self) -> Result<bool, HeadError> {
        match self.paired.phase {
            Phase::ArgumentReply => {
                self.paired.maximum = self.paired.incoming;
                self.paired.phase = Phase::Unfold;
                Ok(true)
            }
            Phase::BinderReply => Ok(false),
            _ => Err(ResourceError::Invariant.into()),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(in super::super) fn advance(
        &mut self,
        pairs: &mut Vec<(ExprId, ExprId)>,
        scope: &Scope<'_>,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        ledger: &mut SessionCacheBudget,
        universes: &mut SharedMemo,
        budget: &mut Budget,
    ) -> Result<Step, HeadError> {
        loop {
            budget.charge_work(1)?;
            match self.paired.phase {
                Phase::Select => {
                    self.paired.incoming = self.left.path.maximum(self.right.path);
                    self.paired.maximum = self.paired.incoming;
                    self.paired.selected = delta::select_sources(
                        self.left.expression,
                        self.right.expression,
                        scope,
                        environment,
                        expressions,
                        levels,
                        names,
                        budget,
                    )?;
                    if self.paired.selected == 0 {
                        self.paired.phase = Phase::Stopped;
                        continue;
                    }
                    if self.paired.selected & 64 != 0
                        && let Some(equal_arity) = same_definition::prepare(
                            self.left.expression,
                            self.right.expression,
                            pairs,
                            expressions,
                            levels,
                            names,
                            ledger,
                            universes,
                            budget,
                        )?
                    {
                        if !equal_arity {
                            self.paired.selected |= 128;
                        }
                        self.paired.phase = Phase::Arguments;
                    } else {
                        self.paired.phase = match self.paired.selected & 12 {
                            4 => Phase::ProbeLeft,
                            8 => Phase::ProbeRight,
                            _ => Phase::Unfold,
                        };
                    }
                }
                Phase::Arguments => {
                    if let Some((left, right)) = pairs.pop() {
                        budget.release_frames(1)?;
                        self.paired.phase = Phase::ArgumentReply;
                        return Ok(Step::Comparison {
                            left,
                            right,
                            incoming: self.paired.incoming,
                        });
                    }
                    self.paired.phase = if self.paired.selected & 128 == 0 {
                        Phase::Equal
                    } else {
                        Phase::Unfold
                    };
                }
                Phase::ProbeLeft | Phase::ProbeRight => {
                    return Ok(Step::Head {
                        root: if self.paired.phase == Phase::ProbeLeft {
                            self.left.expression
                        } else {
                            self.right.expression
                        },
                        incoming: self.paired.incoming,
                        exposure: Exposure::NonDelta,
                    });
                }
                Phase::Unfold => {
                    // An unsuccessful optional shortcut contributes no height.
                    self.paired.maximum = self.paired.incoming;
                    let count = pairs.len();
                    pairs.clear();
                    budget.release_frames(count)?;
                    for (bit, source) in [(1, &mut self.left), (2, &mut self.right)] {
                        if self.paired.selected & bit != 0 {
                            source.expression = delta::unfold(
                                source.expression,
                                self.paired.incoming,
                                pairs,
                                scope,
                                environment,
                                expressions,
                                levels,
                                names,
                                budget,
                            )?;
                        }
                    }
                    self.paired.phase = if self.paired.selected & 1 != 0 {
                        Phase::Left
                    } else {
                        Phase::Right
                    };
                }
                Phase::Left | Phase::Right => {
                    return Ok(Step::Head {
                        root: if self.paired.phase == Phase::Left {
                            self.left.expression
                        } else {
                            self.right.expression
                        },
                        incoming: self.paired.incoming.after_reduction()?,
                        exposure: Exposure::Cheap,
                    });
                }
                Phase::Quick => {
                    self.paired.incoming = self.left.path.maximum(self.right.path);
                    match positive::compare_structure(
                        self.left.expression,
                        self.right.expression,
                        positive::LevelRule::Identity(levels),
                        expressions,
                        names,
                        budget,
                    ) {
                        Ok(()) => {
                            self.paired.maximum = self.paired.incoming;
                            self.paired.phase = Phase::Equal;
                            continue;
                        }
                        Err(HeadError::Unsupported) => (),
                        Err(error) => return Err(error),
                    }
                    let a = expressions.get(self.left.expression, budget)?.kind(
                        expressions,
                        levels,
                        budget,
                    )?;
                    let b = expressions.get(self.right.expression, budget)?.kind(
                        expressions,
                        levels,
                        budget,
                    )?;
                    let equal = match (a, b) {
                        (ExprKind::Pi(..), ExprKind::Pi(..))
                        | (ExprKind::Lambda(..), ExprKind::Lambda(..)) => {
                            // C on this exact matching-binder pair starts with Q's
                            // terminal domain/body rule. No other shape is allowed
                            // to bypass the remaining source-delta procedure.
                            self.paired.phase = Phase::BinderReply;
                            return Ok(Step::Comparison {
                                left: self.left.expression,
                                right: self.right.expression,
                                incoming: self.paired.incoming,
                            });
                        }
                        (ExprKind::Sort(a), ExprKind::Sort(b)) => Some(matches!(
                            levels.with_helpers(names, budget, |h| {
                                h.compare_universes_with(
                                    a,
                                    b,
                                    Some(SharedTable {
                                        memo: &mut *universes,
                                        ledger: &mut *ledger,
                                    }),
                                )
                            })?,
                            UniverseComparison::Equal
                        )),
                        (ExprKind::Natural(a), ExprKind::Natural(b)) => {
                            if environment
                                .natural_constructors(
                                    scope.before,
                                    scope.formation,
                                    scope.expression_end,
                                    expressions,
                                    budget,
                                )?
                                .is_none()
                            {
                                return Err(HeadError::Unsupported);
                            }
                            budget.charge_work(a.len().min(b.len()) as u64)?;
                            Some(a == b)
                        }
                        (ExprKind::String(a), ExprKind::String(b)) => {
                            if environment
                                .string_type(
                                    scope.before,
                                    scope.formation,
                                    scope.expression_end,
                                    expressions,
                                    levels,
                                    budget,
                                )?
                                .is_none()
                            {
                                return Err(HeadError::Unsupported);
                            }
                            budget.charge_work(a.len().min(b.len()) as u64)?;
                            Some(a == b)
                        }
                        _ => None,
                    };
                    self.paired.maximum = self.paired.incoming;
                    self.paired.phase = match equal {
                        Some(true) => Phase::Equal,
                        Some(false) => Phase::Stopped,
                        None => Phase::Select,
                    };
                }
                Phase::Equal => return Ok(Step::Equal(self.paired.maximum)),
                Phase::Stopped => return Ok(Step::Stopped),
                Phase::ArgumentReply | Phase::BinderReply => {
                    return Err(ResourceError::Invariant.into());
                }
            }
        }
    }

    pub(in super::super) fn resume_head_reply(
        &mut self,
        head: Head,
        unchanged: bool,
    ) -> Result<(), HeadError> {
        let phase = self.paired.phase;
        let expected = match phase {
            Phase::ProbeLeft | Phase::ProbeRight => self.paired.incoming,
            Phase::Left | Phase::Right => self.paired.incoming.after_reduction()?,
            _ => return Err(ResourceError::Invariant.into()),
        };
        head.path.height_since(expected)?;
        let source = if matches!(phase, Phase::ProbeLeft | Phase::Left) {
            &mut self.left
        } else {
            &mut self.right
        };
        // Status affects only the non-delta probe. Actual post-delta replies
        // retain their charged route and always proceed to the quick comparison.
        let changed = !unchanged && source.expression != head.expression;
        *source = head;
        self.paired.phase = if matches!(phase, Phase::ProbeLeft | Phase::ProbeRight) {
            self.paired.incoming = self.left.path.maximum(self.right.path);
            if changed { Phase::Quick } else { Phase::Unfold }
        } else if phase == Phase::Left && self.paired.selected & 2 != 0 {
            Phase::Right
        } else {
            Phase::Quick
        };
        Ok(())
    }

    pub(in super::super) fn resume_comparison(
        &mut self,
        decision: Decision,
    ) -> Result<(), HeadError> {
        if !self.comparing() {
            return Err(ResourceError::Invariant.into());
        }
        match decision {
            Decision::Equal(path) => {
                path.height_since(self.paired.incoming)?;
                self.paired.maximum = self.paired.maximum.maximum(path);
                self.paired.phase = if self.paired.phase == Phase::ArgumentReply {
                    Phase::Arguments
                } else {
                    Phase::Equal
                };
            }
            Decision::Different(_) => {
                self.paired.maximum = self.paired.incoming;
                self.paired.phase = if self.paired.phase == Phase::ArgumentReply {
                    Phase::Unfold
                } else {
                    Phase::Stopped
                };
            }
        }
        Ok(())
    }
}
