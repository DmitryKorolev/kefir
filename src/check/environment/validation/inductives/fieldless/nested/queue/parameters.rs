//! One checked parameter context for exact nested keys. Only the syntactic Pi
//! prefix is consumed; constructor-local bound variables remain bound and can
//! never be mistaken for a block parameter. This owner grants no helper authority.
use super::*;
use crate::check::environment::CheckednessMint;
use crate::syntax::expressions::{BinderInfo, binding::Binding};
use crate::syntax::local_context::{CheckedTy, FreeId};

#[derive(Clone, Copy)]
struct Parameter {
    id: FreeId,
    expression: ExprId,
    domain: ExprId,
    name: NameId,
    annotation: BinderInfo,
}
#[derive(Clone, Copy)]
struct Prefix {
    domain: ExprId,
    name: NameId,
    annotation: BinderInfo,
}
const _: () = assert!(size_of::<Parameter>() == 20);
const _: () = assert!(size_of::<Prefix>() == 12);

#[derive(Default)]
pub(super) struct Parameters {
    locals: Vec<Parameter>,
}
impl Parameters {
    pub(super) fn prepare(
        &mut self,
        root: ExprId,
        count: u32,
        work: &mut Working<'_>,
    ) -> Result<(), Stop> {
        if !self.locals.is_empty() {
            return Err(ResourceError::Invariant.into());
        }
        let mut root = root;
        for _ in 0..count {
            let (name, domain, body, annotation) = pi(root, work)?;
            // Audited precondition: root is the checked original first family
            // type, in this declaration and universe scope. Pi formation gives
            // a checked domain; substituting the fresh local transports the
            // checked body to the next iteration. This exact syntactic prefix
            // neither needs a second inference nor grants helper-body evidence.
            let length = self
                .locals
                .len()
                .checked_add(1)
                .ok_or(ResourceError::Counter)?;
            work.budget.grow_vec(&mut self.locals, length)?;
            let id = work.context.enter_checked(
                CheckedTy::checked(domain, CheckednessMint::mint()),
                None,
                name,
                annotation,
                work.expressions,
                work.names,
                work.budget,
            )?;
            // Retain ownership before any fallible append/substitution.
            self.locals.push(Parameter {
                id,
                expression: domain,
                domain,
                name,
                annotation,
            });
            let expression = work.expressions.append(
                ExprKind::Free(id.slot()),
                work.levels,
                work.names,
                work.budget,
            )?;
            self.locals
                .last_mut()
                .ok_or(ResourceError::Invariant)?
                .expression = expression;
            root = substitute(body, expression, work)?;
        }
        Ok(())
    }

    /// Visit a constructor body with precisely the shared checked locals. Its
    /// own parameter domains/annotations are retained for reconstruction, rather
    /// than replaced by the first family's presentation or converted domains.
    /// Precondition: the original constructor type was checked under `scope`'s
    /// signature-only phase, or this is a helper prefix produced by `close`.
    /// Each successful ordered domain comparison licenses substituting the same
    /// common checked local into the remaining prefix. Prefix checkedness alone
    /// is transported; helper bodies still require independent rechecking.
    pub(super) fn with_open<T>(
        &self,
        root: ExprId,
        work: &mut Working<'_>,
        scope: Scope<'_>,
        environment: &Environment,
        visit: impl FnOnce(ExprId, &mut Working<'_>) -> Result<T, Stop>,
    ) -> Result<T, Stop> {
        let mut root = root;
        for parameter in &self.locals {
            let (_, domain, body, _) = pi(root, work)?;
            work.compare_checked_types(
                domain,
                parameter.domain,
                ReductionPath::start(),
                scope,
                environment,
            )?;
            root = substitute(body, parameter.expression, work)?;
        }
        visit(root, work)
    }

    pub(super) fn rewrite(
        &self,
        root: ExprId,
        work: &mut Working<'_>,
        visit: impl FnOnce(ExprId, &mut Working<'_>) -> Result<ExprId, Stop>,
    ) -> Result<ExprId, Stop> {
        let original = root;
        let mut prefix = Vec::new();
        let result = (|| {
            let mut root = root;
            for parameter in &self.locals {
                let (name, domain, body, annotation) = pi(root, work)?;
                push(
                    &mut prefix,
                    Prefix {
                        name,
                        domain,
                        annotation,
                    },
                    work.budget,
                )?;
                root = substitute(body, parameter.expression, work)?;
            }
            let changed = visit(root, work)?;
            if changed == root {
                Ok(original)
            } else {
                self.close_with(changed, prefix.iter().copied(), false, work)
            }
        })();
        release(prefix, work.budget)?;
        result
    }

    pub(super) fn close(&self, root: ExprId, work: &mut Working<'_>) -> Result<ExprId, Stop> {
        self.close_with(
            root,
            self.locals.iter().map(|p| Prefix {
                name: p.name,
                domain: p.domain,
                annotation: p.annotation,
            }),
            false,
            work,
        )
    }
    pub(super) fn recipe(&self, root: ExprId, work: &mut Working<'_>) -> Result<ExprId, Stop> {
        self.close_with(
            root,
            self.locals.iter().map(|p| Prefix {
                name: p.name,
                domain: p.domain,
                annotation: p.annotation,
            }),
            true,
            work,
        )
    }
    fn close_with(
        &self,
        mut root: ExprId,
        prefix: impl DoubleEndedIterator<Item = Prefix> + ExactSizeIterator,
        lambda: bool,
        work: &mut Working<'_>,
    ) -> Result<ExprId, Stop> {
        if prefix.len() != self.locals.len() {
            return Err(ResourceError::Invariant.into());
        }
        for (parameter, original) in self.locals.iter().zip(prefix).rev() {
            root = work.expressions.bind(
                root,
                0,
                Binding::Abstract(&[parameter.id.slot()]),
                work.levels,
                work.names,
                work.budget,
            )?;
            root = work.expressions.append(
                if lambda {
                    ExprKind::Lambda(original.name, original.domain, root, original.annotation)
                } else {
                    ExprKind::Pi(original.name, original.domain, root, original.annotation)
                },
                work.levels,
                work.names,
                work.budget,
            )?;
        }
        Ok(root)
    }

    pub(super) fn apply(&self, root: ExprId, work: &mut Working<'_>) -> Result<ExprId, Stop> {
        let mut root = root;
        for parameter in &self.locals {
            root = work.expressions.append(
                ExprKind::App(root, parameter.expression),
                work.levels,
                work.names,
                work.budget,
            )?;
        }
        Ok(root)
    }
    pub(super) fn retire(self, work: &mut Working<'_>) -> Result<(), ResourceError> {
        let result = (|| {
            for parameter in self.locals.iter().rev() {
                work.context.leave(parameter.id, work.budget)?;
            }
            Ok(())
        })();
        release(self.locals, work.budget)?;
        result
    }
}
fn pi(root: ExprId, work: &mut Working<'_>) -> Result<(NameId, ExprId, ExprId, BinderInfo), Stop> {
    match work.expressions.get(root, work.budget)?.kind(
        work.expressions,
        work.levels,
        work.budget,
    )? {
        ExprKind::Pi(name, domain, body, annotation) => Ok((name, domain, body, annotation)),
        // Unavailable faithful syntactic prefix is a support boundary, never a
        // declaration-level negative or permission to consume a WHNF wrapper.
        _ => Err(Stop::Unsupported),
    }
}
fn substitute(root: ExprId, argument: ExprId, work: &mut Working<'_>) -> Result<ExprId, Stop> {
    Ok(work.expressions.bind(
        root,
        0,
        Binding::Instantiate(&[argument]),
        work.levels,
        work.names,
        work.budget,
    )?)
}
