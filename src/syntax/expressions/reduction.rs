//! One immediate beta/zeta step only. No exposure/normalization/conversion result.
use super::*;
use crate::resource::{Event, ReductionPath};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Rule {
    Beta,
    Zeta,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Step {
    Reduced {
        expression: ExprId,
        rule: Rule,
        path: ReductionPath,
    },
    /// Only these immediate rules failed to match. Delta, further head exposure,
    /// iota and other rules may remain; this is NEVER a normal-form certificate.
    NoBetaZetaRedex,
}
impl Expressions {
    /// Caller supplies well-scoped syntax with binder contexts already opened
    /// to free locals. It must separately validate annotations/values; skipping
    /// them during reduction grants no typing/checkedness. Free ids must remain
    /// active throughout the operation. Every child continuation inherits path.
    /// Failure returns no completed step; partial generated syntax remains owned
    /// by the declaration watermark, and resource exhaustion never rejects.
    pub(crate) fn beta_zeta_step(
        &mut self,
        root: ExprId,
        path: ReductionPath,
        levels: &Levels,
        names: &impl LevelNames,
        b: &mut Budget,
    ) -> Result<Step, ExpressionError> {
        b.charge_work(1)?;
        let (body, value, rule) = match self.get(root, b)?.kind(self, levels, b)? {
            ExprKind::App(function, argument) => {
                match self.get(function, b)?.kind(self, levels, b)? {
                    ExprKind::Lambda(_, _, body, _) => (body, argument, Rule::Beta),
                    _ => return Ok(Step::NoBetaZetaRedex),
                }
            }
            ExprKind::Let(_, _, value, body, _) => (body, value, Rule::Zeta),
            _ => return Ok(Step::NoBetaZetaRedex),
        };
        let next = path.after_reduction()?;
        let expression = self.bind(
            body,
            0,
            binding::Binding::Instantiate(&[value]),
            levels,
            names,
            b,
        )?;
        // Count the completed rewrite, never a match attempt or failed binding.
        b.observe(Event::Reductions, 1);
        Ok(Step::Reduced {
            expression,
            rule,
            path: next,
        })
    }
}
