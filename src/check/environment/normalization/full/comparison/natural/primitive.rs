//! C9 arithmetic operand observations, scoped to one checked comparison pair.
//! Only publication under committed intrinsic authority licenses a restart.
use super::*;
use crate::check::environment::constant_use::ConstantUse;
use crate::syntax::levels::NameId;

pub(in super::super) enum Step {
    Head {
        root: ExprId,
        incoming: ReductionPath,
    },
    Complete(Option<(Head, Head)>),
}

#[derive(Clone, Copy)]
enum Phase {
    Begin,
    AwaitLeft,
    LeftReady,
    AwaitRight,
    RightReady,
    Done,
    Failed,
}

/// The driver fixes scope, table origins and checkedness for this owner's life.
/// Observations are not judgments or cached certificates. Errors end the owner;
/// no partially observed route or ordinary delta result can authorize a restart.
pub(in super::super) struct Primitive {
    roots: [ExprId; 2],
    outputs: [Head; 2],
    incoming: ReductionPath,
    right: ExprId,
    name: NameId,
    left: Head,
    observed: Head,
    side: u8,
    changed: bool,
    phase: Phase,
}
const _: () = assert!(std::mem::size_of::<Primitive>() <= 80);

impl Primitive {
    pub(in super::super) fn new(left: ExprId, right: ExprId, incoming: ReductionPath) -> Self {
        let a = Head {
            expression: left,
            path: incoming,
        };
        let b = Head {
            expression: right,
            path: incoming,
        };
        Self {
            roots: [left, right],
            outputs: [a, b],
            incoming,
            right,
            // This name is inaccessible until Begin validates a real constant.
            name: NameId(0),
            left: a,
            observed: a,
            side: 0,
            changed: false,
            phase: Phase::Begin,
        }
    }

    pub(in super::super) fn resume(&mut self, observed: Head) -> Result<(), HeadError> {
        let next = match self.phase {
            Phase::AwaitLeft => Phase::LeftReady,
            Phase::AwaitRight => Phase::RightReady,
            _ => {
                self.phase = Phase::Failed;
                return Err(ResourceError::Invariant.into());
            }
        };
        self.phase = Phase::Failed;
        observed.path.height_since(self.incoming)?;
        self.observed = observed;
        self.phase = next;
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(in super::super) fn advance(
        &mut self,
        scope: &Scope<'_>,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &Levels,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Step, HeadError> {
        let result = self.advance_inner(scope, environment, expressions, levels, names, budget);
        if result.is_err() {
            self.phase = Phase::Failed;
        }
        result
    }

    fn next_side(&mut self) {
        self.side += 1;
        self.phase = Phase::Begin;
    }

    #[allow(clippy::too_many_arguments)]
    fn advance_inner(
        &mut self,
        scope: &Scope<'_>,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &Levels,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Step, HeadError> {
        loop {
            match self.phase {
                Phase::Begin => {
                    if self.side == 2 {
                        self.phase = Phase::Done;
                        return Ok(Step::Complete(
                            self.changed.then_some((self.outputs[0], self.outputs[1])),
                        ));
                    }
                    let root = self.roots[self.side as usize];
                    if scope.formation.is_some() || expressions.get(root, budget)?.has_free() {
                        self.next_side();
                        continue;
                    }
                    let ExprKind::App(function, right) =
                        expressions
                            .get(root, budget)?
                            .kind(expressions, levels, budget)?
                    else {
                        self.next_side();
                        continue;
                    };
                    let ExprKind::App(head, left) =
                        expressions
                            .get(function, budget)?
                            .kind(expressions, levels, budget)?
                    else {
                        self.next_side();
                        continue;
                    };
                    let ExprKind::Constant(name, arguments) =
                        expressions
                            .get(head, budget)?
                            .kind(expressions, levels, budget)?
                    else {
                        self.next_side();
                        continue;
                    };
                    let site = ConstantUse {
                        name,
                        arguments,
                        parameters: scope.parameters,
                        before: scope.before,
                        formation: scope.formation,
                        mode: scope.mode,
                        expression_end: scope.expression_end,
                        level_end: scope.level_end,
                    };
                    if environment
                        .natural_arithmetic_kind(&site, levels, names, budget)?
                        .is_none()
                    {
                        self.next_side();
                        continue;
                    }
                    self.name = name;
                    self.right = right;
                    self.phase = Phase::AwaitLeft;
                    return Ok(Step::Head {
                        root: left,
                        incoming: self.incoming,
                    });
                }
                Phase::LeftReady => {
                    let numeric = match expressions.get(self.observed.expression, budget)?.kind(
                        expressions,
                        levels,
                        budget,
                    )? {
                        ExprKind::Natural(_) => true,
                        ExprKind::Constant(name, []) => {
                            let Some((_, zero, _)) = environment.natural_constructors(
                                scope.before,
                                scope.formation,
                                scope.expression_end,
                                expressions,
                                budget,
                            )?
                            else {
                                self.next_side();
                                continue;
                            };
                            names.summary(name, budget)?.canonical
                                == names.summary(zero, budget)?.canonical
                        }
                        _ => false,
                    };
                    if !numeric {
                        self.next_side();
                        continue;
                    }
                    self.left = self.observed;
                    self.phase = Phase::AwaitRight;
                    return Ok(Step::Head {
                        root: self.right,
                        incoming: self.incoming,
                    });
                }
                Phase::RightReady => {
                    let path = self.left.path.maximum(self.observed.path);
                    let site = ConstantUse {
                        name: self.name,
                        arguments: &[],
                        parameters: scope.parameters,
                        before: scope.before,
                        formation: scope.formation,
                        mode: scope.mode,
                        expression_end: scope.expression_end,
                        level_end: scope.level_end,
                    };
                    if let Some(digits) = environment.natural_arithmetic_result(
                        &site,
                        expressions.get(self.left.expression, budget)?.kind(
                            expressions,
                            levels,
                            budget,
                        )?,
                        expressions.get(self.observed.expression, budget)?.kind(
                            expressions,
                            levels,
                            budget,
                        )?,
                        levels,
                        names,
                        budget,
                    )? {
                        let result = (|| -> Result<Head, HeadError> {
                            let path = path.after_reduction()?;
                            let expression = expressions.append(
                                ExprKind::Natural(digits.as_bytes()),
                                levels,
                                names,
                                budget,
                            )?;
                            budget.observe(crate::resource::Event::Reductions, 1);
                            Ok(Head { expression, path })
                        })();
                        // Retire the temporary reservation even when path or syntax
                        // publication fails. No partial result escapes either error.
                        digits.retire(budget)?;
                        self.outputs[self.side as usize] = result?;
                        self.changed = true;
                    }
                    self.next_side();
                }
                Phase::AwaitLeft | Phase::AwaitRight | Phase::Done | Phase::Failed => {
                    return Err(ResourceError::Invariant.into());
                }
            }
        }
    }
}
