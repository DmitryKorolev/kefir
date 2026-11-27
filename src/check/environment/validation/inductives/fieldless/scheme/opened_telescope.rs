//! Check closed generated telescopes under injective renaming in signature-only staging.
use super::*;

#[derive(Clone, Copy)]
enum Query {
    Rule(ExprId),
    RecursorType,
}

// These IDs are innermost first, matching Binding::Instantiate. The bound
// limits only this query; ordinary formation and applied checking stay available.
struct Assumptions {
    args: [ExprId; 64],
    ids: [u32; 64],
    len: usize,
}

impl Assumptions {
    fn new(root: ExprId) -> Self {
        Self {
            args: [root; 64],
            ids: [0; 64],
            len: 0,
        }
    }

    fn push(&mut self, work: &mut Working<'_>, arg: ExprId) -> Result<bool, Stop> {
        let ExprKind::Free(id) = kind(work, arg)? else {
            return Ok(false);
        };
        if self.len == self.args.len() {
            return Ok(false);
        }
        work.budget.charge_work(self.len as u64 + 1)?;
        if self.ids[..self.len].contains(&id)
            || work.context.get(id, work.budget)?.value().is_some()
        {
            return Ok(false);
        }
        self.args[self.len] = arg;
        self.ids[self.len] = id;
        self.len += 1;
        Ok(true)
    }
}

/// All callers independently check universe scope on the closed source root.
/// The active locals and the signature-only stage remain fixed through cleanup.
fn query(
    work: &mut Working<'_>,
    mut head: ExprId,
    bindings: &Assumptions,
    query: Query,
    scope: Scope<'_>,
    environment: &Environment,
) -> Result<bool, Stop> {
    let args = &bindings.args[..bindings.len];
    let ids = &bindings.ids[..bindings.len];
    let expressions = work.expressions.watermark();
    let levels = work.levels.len();
    // Binding and schema matching keep their scratch local; formation_check
    // retires its value arena before returning. Neither operation enters a
    // caller local or installs a signature. Every root retained by the caller
    // therefore predates these marks on both success and refusal.
    let result = (|| {
        if let Query::Rule(expected) = query
            && work.expressions.get(expected, work.budget)?.has_free()
        {
            let abstracted = work.expressions.bind(
                expected,
                0,
                Binding::Abstract(ids),
                work.levels,
                work.names,
                work.budget,
            )?;
            if work.expressions.get(abstracted, work.budget)?.has_free() {
                return Ok(false);
            }
        }
        for i in (0..args.len()).rev() {
            let (dom, body) = match (query, kind(work, head)?) {
                (Query::Rule(_), ExprKind::Lambda(_, dom, body, _))
                | (Query::RecursorType, ExprKind::Pi(_, dom, body, _)) => (dom, body),
                _ => return Ok(false),
            };
            let opened = if work.expressions.get(dom, work.budget)?.loose_range() == 0 {
                dom
            } else {
                work.expressions.bind(
                    dom,
                    0,
                    Binding::Instantiate(&args[i + 1..]),
                    work.levels,
                    work.names,
                    work.budget,
                )?
            };
            let ty = work.context.get(ids[i], work.budget)?.ty();
            if opened != ty && !matches(work, opened, ty)? {
                return Ok(false);
            }
            head = body;
        }
        let opened = work.expressions.bind(
            head,
            0,
            Binding::Instantiate(args),
            work.levels,
            work.names,
            work.budget,
        )?;
        // All opened domains match the checked assumption types. Distinct
        // variables and support of the original expected type permit the
        // inverse renaming of this independently established body judgment.
        match query {
            Query::Rule(expected) => {
                work.check_formation_rule(opened, expected, scope, environment)
            }
            // Each matched Pi domain already has a sort. This consumer only
            // asks for existence of the iterated imax of those sorts and the
            // checked suffix sort; neither a level nor a path escapes.
            Query::RecursorType => Ok(work
                .try_formation_sort(opened, scope, environment)?
                .is_some()),
        }
    })()?;
    work.retire_rule_probe(expressions, levels)?;
    Ok(result)
}

/// Check the actual closed lambda applied to the actual arguments.
pub(super) fn check(
    work: &mut Working<'_>,
    rhs: ExprId,
    applied: ExprId,
    expected: ExprId,
    scope: Scope<'_>,
    environment: &Environment,
) -> Result<bool, Stop> {
    if scope.formation.is_none() || scope.mode != Mode::Safe || rhs == applied {
        return Ok(false);
    }
    let root = work.expressions.get(rhs, work.budget)?;
    if root.has_free()
        || root.loose_range() != 0
        || work.expressions.get(expected, work.budget)?.loose_range() != 0
    {
        return Ok(false);
    }
    let mut bindings = Assumptions::new(rhs);
    let mut head = applied;
    while head != rhs {
        let ExprKind::App(f, a) = kind(work, head)? else {
            return Ok(false);
        };
        if !bindings.push(work, a)? {
            return Ok(false);
        }
        head = f;
    }
    let result = query(
        work,
        rhs,
        &bindings,
        Query::Rule(expected),
        scope,
        environment,
    )?;
    Ok(result)
}

impl Scratch {
    /// The caller requests formation only. Its original ordinary check ignores
    /// the returned path. The recursor itself has not entered the staged signature.
    pub(in super::super) fn formed_recursor_type(
        &self,
        work: &mut Working<'_>,
        root: ExprId,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<bool, Stop> {
        if scope.formation.is_none() || scope.mode != Mode::Safe {
            return Ok(false);
        }
        let node = work.expressions.get(root, work.budget)?;
        if node.has_free() || node.loose_range() != 0 {
            return Ok(false);
        }
        let base = self.parameters + self.indices;
        let mut bindings = Assumptions::new(root);
        for b in self.binders[..self.parameters]
            .iter()
            .chain(&self.binders[base..])
            .rev()
        {
            if !bindings.push(work, b.expression)? {
                return Ok(false);
            }
        }
        if bindings.len == 0 {
            return Ok(false);
        }
        let result = query(
            work,
            root,
            &bindings,
            Query::RecursorType,
            scope,
            environment,
        )?;
        Ok(result)
    }
}
