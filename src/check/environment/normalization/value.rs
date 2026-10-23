//! Demand-owned positive conversion of closed monomorphic values.
//!
//! The imported graph stays immutable. Each delayed value belongs to one
//! ordinary driver call with fixed checked operands, context and frontiers.
//! One value id denotes one computation for the evaluator's lifetime: closed
//! syntax, applications and recursor results are shared by exact keys, a bound
//! variable denotes its environment's value, and forcing only replaces a value
//! with an equal one. A miss or unsupported form supplies no judgment.
use super::*;
use crate::resource::SessionCacheBudget;

const NONE: u32 = u32::MAX;
const MAX_SPINE: usize = 16;
const MAX_VALUE_DEPTH: usize = 9_000;
const MAX_FORCE_CALLS: u32 = 400_000;

// Independent premises share an inherited producer path; sequential forcing
// still extends it. The charged worklist stores twelve bytes per pair.
type ComparisonPair = (u32, u32, ReductionPath);
const _: () = assert!(size_of::<ComparisonPair>() == 12);

#[derive(Clone, Copy, Debug)]
enum Value {
    Delayed {
        expression: ExprId,
        environment: u32,
    },
    Active,
    Lambda {
        body: ExprId,
        environment: u32,
    },
    Neutral {
        head: ExprId,
        spine: u32,
    },
    Whnf {
        head: ExprId,
        spine: u32,
    },
    Canonical {
        head: ExprId,
        spine: u32,
    },
    Complete {
        head: u32,
        height: u32,
    },
}

#[derive(Clone, Copy)]
struct Binding {
    parent: u32,
    value: u32,
    depth: u32,
}

#[derive(Clone, Copy)]
struct Argument {
    previous: u32,
    value: u32,
    len: u32,
}

/// An unforced application chain peeled to its head syntax. `arguments` holds
/// the peeled argument slots in peel order — outermost application first, the
/// reverse of application order.
struct DelayedApplication {
    head: ExprId,
    arguments: [u32; MAX_SPINE],
    len: usize,
}

#[derive(Clone, Copy, Default)]
struct Entry {
    left: u32,
    right: u32,
    result: u32,
    tag: u32,
}

#[derive(Default)]
struct Table {
    entries: Vec<Entry>,
    used: usize,
}

impl Table {
    fn hash(tag: u32, left: u32, right: u32) -> usize {
        let mut h = u64::from(left) ^ (u64::from(right) << 32);
        h ^= u64::from(tag).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        h ^= h >> 33;
        h = h.wrapping_mul(0xc2b2_ae3d_27d4_eb4f);
        (h ^ (h >> 29)) as usize
    }

    fn position(entries: &[Entry], tag: u32, left: u32, right: u32) -> Option<usize> {
        let mask = entries.len().checked_sub(1)?;
        let mut slot = Self::hash(tag, left, right) & mask;
        for _ in 0..entries.len() {
            let e = entries[slot];
            if e.tag == 0 || (e.tag == tag && e.left == left && e.right == right) {
                return Some(slot);
            }
            slot = (slot + 1) & mask;
        }
        None
    }

    fn get(&self, tag: u32, left: u32, right: u32) -> Option<u32> {
        let slot = Self::position(&self.entries, tag, left, right)?;
        (self.entries[slot].tag != 0).then_some(self.entries[slot].result)
    }

    fn insert(
        &mut self,
        tag: u32,
        left: u32,
        right: u32,
        result: u32,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        if self.used + 1 > self.entries.len() * 3 / 4 {
            let cap = self.entries.len().checked_mul(2).unwrap_or(0).max(32);
            if cap == 0 {
                return Err(ResourceError::Counter);
            }
            let mut next = Vec::new();
            b.grow_vec(&mut next, cap)?;
            next.resize(cap, Entry::default());
            for e in self.entries.iter().copied().filter(|e| e.tag != 0) {
                let slot = Self::position(&next, e.tag, e.left, e.right)
                    .ok_or(ResourceError::Invariant)?;
                next[slot] = e;
            }
            let old = std::mem::replace(&mut self.entries, next);
            release(old, b)?;
        }
        let slot =
            Self::position(&self.entries, tag, left, right).ok_or(ResourceError::Invariant)?;
        if self.entries[slot].tag == 0 {
            self.used += 1;
        }
        self.entries[slot] = Entry {
            left,
            right,
            result,
            tag,
        };
        Ok(())
    }
}

fn release<T>(values: Vec<T>, b: &mut Budget) -> Result<(), ResourceError> {
    let bytes = values
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)?;
    drop(values);
    b.release(bytes as u64)
}

struct Evaluator<'a, 's> {
    scope: Scope<'s>,
    declarations: &'a Environment,
    expressions: &'a mut Expressions,
    levels: &'a mut Levels,
    names: &'a Names,
    budget: &'a mut Budget,
    values: Vec<Value>,
    bindings: Vec<Binding>,
    arguments: Vec<Argument>,
    table: Table,
    transport: super::super::instantiation::Cache,
    transport_budget: SessionCacheBudget,
    path: ReductionPath,
    depth: usize,
    depth_limit: usize,
    force_calls: u32,
}

#[derive(Clone, Copy, Debug)]
enum EvaluationError {
    Unsupported,
    Resource(ResourceError),
    Use(UseError),
}

fn unsupported<T>() -> Result<T, EvaluationError> {
    Err(EvaluationError::Unsupported)
}

impl From<ResourceError> for EvaluationError {
    fn from(value: ResourceError) -> Self {
        Self::Resource(value)
    }
}
impl From<UseError> for EvaluationError {
    fn from(value: UseError) -> Self {
        Self::Use(value)
    }
}
impl From<crate::syntax::expressions::ExpressionError> for EvaluationError {
    fn from(value: crate::syntax::expressions::ExpressionError) -> Self {
        match value {
            crate::syntax::expressions::ExpressionError::Resource(e) => Self::Resource(e),
            other => Self::Use(UseError::Expression(other)),
        }
    }
}

impl Evaluator<'_, '_> {
    fn push_value(&mut self, value: Value) -> Result<u32, EvaluationError> {
        let slot = u32::try_from(self.values.len()).map_err(|_| ResourceError::Counter)?;
        let needed = self.values.len() + 1;
        self.budget.grow_vec(&mut self.values, needed)?;
        self.values.push(value);
        Ok(slot)
    }

    fn delayed(&mut self, expression: ExprId, environment: u32) -> Result<u32, EvaluationError> {
        let node = self.expressions.get(expression, self.budget)?;
        let needed = node.loose_range() as usize;
        // A bound variable denotes the value its environment already holds:
        // forcing a fresh wrapper would only look that value up and force it.
        // Returning it keeps its identity, so forcing, apply/recursor entries
        // and the comparison's identity check see one value, not a copy.
        // Invariant: no `Value::Delayed` ever holds bound-variable syntax.
        if let ExprKind::Bound(index) = node.kind(self.expressions, self.levels, self.budget)? {
            // The same scope bound as every other open syntax: an index the
            // route does not track stays unsupported, never a lookup.
            if needed > 64 {
                return unsupported();
            }
            if environment == NONE {
                return Err(ResourceError::Invariant.into());
            }
            // Walks at most `needed` (<= 64) parents; an environment shallower
            // than the index ends in an invariant error, as the scope check
            // below reports for other open syntax.
            return self.lookup(environment, index);
        }
        // Closed syntax has no lexical dependency and can share one delayed
        // value throughout this comparison. Other open syntax keeps its exact
        // environment and is not interned.
        let environment = self.scope_environment(needed, environment)?;
        if environment == NONE
            && let Some(value) = self.table.get(1, expression.slot(), environment)
        {
            return Ok(value);
        }
        let value = self.push_value(Value::Delayed {
            expression,
            environment,
        })?;
        if environment == NONE {
            self.table
                .insert(1, expression.slot(), environment, value, self.budget)?;
        }
        Ok(value)
    }

    fn scope_environment(
        &mut self,
        needed: usize,
        environment: u32,
    ) -> Result<u32, EvaluationError> {
        if needed == 0 {
            return Ok(NONE);
        }
        if needed > 64 {
            return unsupported();
        }
        let current_depth = self
            .bindings
            .get(environment as usize)
            .ok_or(ResourceError::Invariant)?
            .depth as usize;
        if current_depth < needed {
            return Err(ResourceError::Invariant.into());
        }
        // Only the closest `needed` bindings are observable. Extra parents may
        // remain attached: nonclosed delayed values are never interned by the
        // environment handle, and their owner is this single comparison.
        Ok(environment)
    }

    fn extend(&mut self, environment: u32, value: u32) -> Result<u32, EvaluationError> {
        let slot = u32::try_from(self.bindings.len()).map_err(|_| ResourceError::Counter)?;
        let depth = if environment == NONE {
            1
        } else {
            self.bindings
                .get(environment as usize)
                .ok_or(ResourceError::Invariant)?
                .depth
                .checked_add(1)
                .ok_or(ResourceError::Counter)?
        };
        let needed = self.bindings.len() + 1;
        self.budget.grow_vec(&mut self.bindings, needed)?;
        self.bindings.push(Binding {
            parent: environment,
            value,
            depth,
        });
        Ok(slot)
    }

    fn lookup(&self, mut environment: u32, index: u32) -> Result<u32, EvaluationError> {
        for _ in 0..index {
            environment = self
                .bindings
                .get(environment as usize)
                .ok_or(ResourceError::Invariant)?
                .parent;
        }
        Ok(self
            .bindings
            .get(environment as usize)
            .ok_or(ResourceError::Invariant)?
            .value)
    }

    fn step(&mut self) -> Result<(), EvaluationError> {
        self.path = self.path.after_reduction()?;
        self.budget.observe(Event::Reductions, 1);
        Ok(())
    }

    fn apply(&mut self, function: u32, argument: u32) -> Result<u32, EvaluationError> {
        let head = self.force(function)?;
        let cacheable = matches!(
            self.values[head as usize],
            Value::Neutral { .. } | Value::Whnf { .. } | Value::Canonical { .. }
        );
        if cacheable && let Some(result) = self.table.get(3, head, argument) {
            return Ok(result);
        }
        let result = match self.values[head as usize] {
            Value::Lambda { body, environment } => {
                self.step()?;
                let environment = self.extend(environment, argument)?;
                self.delayed(body, environment)?
            }
            Value::Neutral { head, spine }
            | Value::Whnf { head, spine }
            | Value::Canonical { head, spine } => {
                let len = if spine == NONE {
                    1
                } else {
                    self.arguments[spine as usize]
                        .len
                        .checked_add(1)
                        .ok_or(ResourceError::Counter)?
                };
                if len as usize > MAX_SPINE {
                    return unsupported();
                }
                let node =
                    u32::try_from(self.arguments.len()).map_err(|_| ResourceError::Counter)?;
                let needed = self.arguments.len() + 1;
                self.budget.grow_vec(&mut self.arguments, needed)?;
                self.arguments.push(Argument {
                    previous: spine,
                    value: argument,
                    len,
                });
                self.push_value(Value::Neutral { head, spine: node })?
            }
            _ => return Err(ResourceError::Invariant.into()),
        };
        if cacheable {
            self.table.insert(3, head, argument, result, self.budget)?;
        }
        Ok(result)
    }

    fn spine(&self, spine: u32) -> Result<([u32; MAX_SPINE], usize), EvaluationError> {
        let mut values = [NONE; MAX_SPINE];
        if spine == NONE {
            return Ok((values, 0));
        }
        let len = self
            .arguments
            .get(spine as usize)
            .ok_or(ResourceError::Invariant)?
            .len as usize;
        if len > MAX_SPINE {
            return unsupported();
        }
        let mut next = spine;
        for slot in values[..len].iter_mut().rev() {
            let item = self
                .arguments
                .get(next as usize)
                .ok_or(ResourceError::Invariant)?;
            *slot = item.value;
            next = item.previous;
        }
        if next != NONE {
            return Err(ResourceError::Invariant.into());
        }
        Ok((values, len))
    }

    /// Peel an unforced application chain down to its head syntax without
    /// forcing anything. The peeled argument slots are built exactly as the
    /// forced evaluation would build them: `force_expression` delays every
    /// application argument in the application's own environment. Chains
    /// longer than `MAX_SPINE` and non-constant heads keep the forced
    /// comparison, whose `apply` refuses or unfolds them the same way it
    /// already does.
    fn delayed_application_spine(
        &mut self,
        value: u32,
    ) -> Result<Option<DelayedApplication>, EvaluationError> {
        let Value::Delayed {
            mut expression,
            environment,
        } = self.values[value as usize]
        else {
            return Ok(None);
        };
        let mut arguments = [NONE; MAX_SPINE];
        let mut len = 0usize;
        loop {
            let kind = self.expressions.get(expression, self.budget)?.kind(
                self.expressions,
                self.levels,
                self.budget,
            )?;
            match kind {
                ExprKind::App(function, argument) => {
                    if len == MAX_SPINE {
                        return Ok(None);
                    }
                    arguments[len] = self.delayed(argument, environment)?;
                    len += 1;
                    expression = function;
                }
                ExprKind::Constant(..) => {
                    return Ok(Some(DelayedApplication {
                        head: expression,
                        arguments,
                        len,
                    }));
                }
                _ => return Ok(None),
            }
        }
    }

    /// Same-head argument quick check. Two unforced applications of
    /// one constant head are equal when their arguments are: the same
    /// canonical constant with equal levels is one constant value — the same
    /// identity the forced comparison accepts — and application is congruent.
    /// Discharges the pair into argument pairs, in peel order reversed so the
    /// pop order matches the forced comparison's. Returns false — the caller
    /// then forces — for any pair without this shape; the check never draws a
    /// negative conclusion.
    fn same_head_arguments(
        &mut self,
        left: u32,
        right: u32,
        pairs: &mut Vec<ComparisonPair>,
    ) -> Result<bool, EvaluationError> {
        let Some(a) = self.delayed_application_spine(left)? else {
            return Ok(false);
        };
        let Some(z) = self.delayed_application_spine(right)? else {
            return Ok(false);
        };
        if a.len != z.len {
            return Ok(false);
        }
        let ak = self.expressions.get(a.head, self.budget)?.kind(
            self.expressions,
            self.levels,
            self.budget,
        )?;
        let zk = self.expressions.get(z.head, self.budget)?.kind(
            self.expressions,
            self.levels,
            self.budget,
        )?;
        let (ExprKind::Constant(an, al), ExprKind::Constant(zn, zl)) = (ak, zk) else {
            return Ok(false);
        };
        if al != zl
            || self.names.summary(an, self.budget)?.canonical
                != self.names.summary(zn, self.budget)?.canonical
        {
            return Ok(false);
        }
        let needed = pairs.len() + a.len;
        self.budget.grow_vec(pairs, needed)?;
        for index in (0..a.len).rev() {
            pairs.push((a.arguments[index], z.arguments[index], self.path));
        }
        Ok(true)
    }

    fn force(&mut self, value: u32) -> Result<u32, EvaluationError> {
        self.force_calls = self
            .force_calls
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        if self.force_calls > MAX_FORCE_CALLS {
            return unsupported();
        }
        self.depth += 1;
        if self.depth > self.depth_limit {
            self.depth -= 1;
            return unsupported();
        }
        let result = self.force_inner(value);
        self.depth -= 1;
        result
    }

    fn force_inner(&mut self, value: u32) -> Result<u32, EvaluationError> {
        self.budget.charge_work(1)?;
        let current = *self
            .values
            .get(value as usize)
            .ok_or(ResourceError::Invariant)?;
        match current {
            Value::Complete { head, height } => {
                self.path = self.path.after_height(height)?;
                let mut resolved = head;
                for _ in 0..MAX_VALUE_DEPTH {
                    let Some(Value::Complete { head: next, .. }) =
                        self.values.get(resolved as usize)
                    else {
                        self.values[value as usize] = Value::Complete {
                            head: resolved,
                            height,
                        };
                        return Ok(resolved);
                    };
                    self.budget.charge_work(1)?;
                    resolved = *next;
                }
                unsupported()
            }
            Value::Active => unsupported(),
            Value::Lambda { .. } => Ok(value),
            Value::Whnf { .. } => Ok(value),
            Value::Canonical { .. } => Ok(value),
            Value::Delayed {
                expression,
                environment,
            } => {
                let incoming = self.path;
                self.values[value as usize] = Value::Active;
                let result = self.force_expression(expression, environment);
                match result {
                    Ok(head) => {
                        let height = self.path.height_since(incoming)?;
                        self.values[value as usize] = Value::Complete { head, height };
                        Ok(head)
                    }
                    Err(error) => Err(error),
                }
            }
            Value::Neutral { head, spine } => self.force_neutral(value, head, spine),
        }
    }

    fn force_expression(
        &mut self,
        expression: ExprId,
        environment: u32,
    ) -> Result<u32, EvaluationError> {
        let kind = self.expressions.get(expression, self.budget)?.kind(
            self.expressions,
            self.levels,
            self.budget,
        )?;
        match kind {
            // `delayed` resolves every bound variable to its environment's
            // value, so no delayed value holds one.
            ExprKind::Bound(_) => Err(ResourceError::Invariant.into()),
            ExprKind::App(function, argument) => {
                let f = self.delayed(function, environment)?;
                let a = self.delayed(argument, environment)?;
                let applied = self.apply(f, a)?;
                self.force(applied)
            }
            ExprKind::Lambda(_, _, body, _) => self.push_value(Value::Lambda { body, environment }),
            ExprKind::Let(_, _, value, body, _) => {
                let value = self.delayed(value, environment)?;
                self.step()?;
                let env = self.extend(environment, value)?;
                let body = self.delayed(body, env)?;
                self.force(body)
            }
            ExprKind::Constant(_, args) if args.len() <= 8 => {
                let neutral = self.push_value(Value::Neutral {
                    head: expression,
                    spine: NONE,
                })?;
                self.force(neutral)
            }
            _ => unsupported(),
        }
    }

    fn force_neutral(
        &mut self,
        value: u32,
        head: ExprId,
        spine: u32,
    ) -> Result<u32, EvaluationError> {
        let incoming = self.path;
        let (arguments, len) = self.spine(spine)?;
        let ExprKind::Constant(name, levels) = self.expressions.get(head, self.budget)?.kind(
            self.expressions,
            self.levels,
            self.budget,
        )?
        else {
            return Err(ResourceError::Invariant.into());
        };
        if levels.len() > 8 {
            return unsupported();
        }
        let mut universe = [LevelId::ZERO; 8];
        universe[..levels.len()].copy_from_slice(levels);
        let universe = &universe[..levels.len()];
        let use_site = ConstantUse {
            name,
            arguments: universe,
            parameters: self.scope.parameters,
            before: self.scope.before,
            formation: self.scope.formation,
            mode: self.scope.mode,
            expression_end: self.scope.expression_end,
            level_end: self.scope.level_end,
        };
        match self.declarations.delta_step_with_cache(
            use_site,
            self.path,
            self.expressions,
            self.levels,
            self.names,
            Some((&mut self.transport, &mut self.transport_budget)),
            self.budget,
        )? {
            DeltaStep::Unfolded { expression, path } => {
                self.path = path;
                let mut result = self.delayed(expression, NONE)?;
                for &argument in &arguments[..len] {
                    result = self.apply(result, argument)?;
                }
                let result = self.force(result)?;
                let height = self.path.height_since(incoming)?;
                self.values[value as usize] = Value::Complete {
                    head: result,
                    height,
                };
                Ok(result)
            }
            DeltaStep::Recursor => {
                let result = self.force_recursor(value, name, universe, &arguments[..len])?;
                if result != value {
                    let height = self.path.height_since(incoming)?;
                    self.values[value as usize] = Value::Complete {
                        head: result,
                        height,
                    };
                } else {
                    self.values[value as usize] = Value::Whnf { head, spine };
                }
                Ok(result)
            }
            DeltaStep::NoDelta => {
                self.values[value as usize] = Value::Whnf { head, spine };
                Ok(value)
            }
            DeltaStep::Quotient(_) => unsupported(),
        }
    }

    fn force_canonical_major(&mut self, value: u32) -> Result<u32, EvaluationError> {
        let major = self.force(value)?;
        // This certificate belongs to the canonicalization operation on the
        // exact ordinary WHNF, not to the shared representative. Ordinary
        // forcing has already charged its own prefix and never reads tag 6.
        if let Some(certificate) = self.table.get(6, major, NONE) {
            let Value::Complete { head, height } = self.values[certificate as usize] else {
                return Err(ResourceError::Invariant.into());
            };
            self.path = self.path.after_height(height)?;
            return Ok(head);
        }
        let incoming = self.path;
        let (head, spine) = match self.values[major as usize] {
            Value::Canonical { .. } => return Ok(major),
            Value::Neutral { head, spine } | Value::Whnf { head, spine } => (head, spine),
            _ => return unsupported(),
        };
        let ExprKind::Constant(name, _) = self.expressions.get(head, self.budget)?.kind(
            self.expressions,
            self.levels,
            self.budget,
        )?
        else {
            return unsupported();
        };
        let (arguments, len) = self.spine(spine)?;
        // canonical_constructor recurses back here for a unary constructor
        // child after `force` has already released its depth. Holding one
        // level across that recursion makes the next level's `force` check
        // see the whole chain, so the native stack stays bounded by
        // depth_limit and an over-long chain becomes unsupported.
        self.depth += 1;
        let result = self.canonical_constructor(major, name, head, &arguments[..len]);
        self.depth -= 1;
        let result = result?;
        if result != major {
            let height = self.path.height_since(incoming)?;
            let certificate = self.push_value(Value::Complete {
                head: result,
                height,
            })?;
            self.table
                .insert(6, major, NONE, certificate, self.budget)?;
        }
        Ok(result)
    }

    fn canonical_constructor(
        &mut self,
        value: u32,
        name: NameId,
        head: ExprId,
        arguments: &[u32],
    ) -> Result<u32, EvaluationError> {
        let before = self.scope.before.min(self.declarations.len());
        let Some(constructor) =
            self.declarations
                .constructor(name, before, self.names, self.budget)?
        else {
            return Ok(value);
        };
        let Some(family) =
            self.declarations
                .inductive(constructor.family, before, self.names, self.budget)?
        else {
            return Ok(value);
        };
        let rule = family
            .constructors
            .get(constructor.index as usize)
            .ok_or(ResourceError::Invariant)?;
        if family.num_params != 0
            || rule.num_fields as usize != arguments.len()
            || arguments.len() > 1
        {
            return Ok(value);
        }
        let child = if let Some(&child) = arguments.first() {
            self.force_canonical_major(child)?
        } else {
            NONE
        };
        if let Some(existing) = self.table.get(4, head.slot(), child) {
            return Ok(existing);
        }
        let canonical = if arguments.len() == 1 {
            // A ready child is valid under the completed canonicalization
            // prefix. Keep it in a separate representative: replacing the
            // ordinary spine would erase the original child's replay height.
            let spine = u32::try_from(self.arguments.len()).map_err(|_| ResourceError::Counter)?;
            self.budget
                .grow_vec(&mut self.arguments, spine as usize + 1)?;
            self.arguments.push(Argument {
                previous: NONE,
                value: child,
                len: 1,
            });
            self.push_value(Value::Canonical { head, spine })?
        } else {
            self.values[value as usize] = Value::Canonical { head, spine: NONE };
            value
        };
        self.table
            .insert(4, head.slot(), child, canonical, self.budget)?;
        Ok(canonical)
    }

    fn force_recursor(
        &mut self,
        value: u32,
        name: NameId,
        universe: &[LevelId],
        arguments: &[u32],
    ) -> Result<u32, EvaluationError> {
        let recursor = self
            .declarations
            .recursor(
                name,
                self.scope.before.min(self.declarations.len()),
                self.names,
                self.budget,
            )?
            .ok_or(EvaluationError::Unsupported)?;
        if recursor.k || recursor.num_indices != 0 {
            return unsupported();
        }
        let prefix = recursor.common_prefix as usize;
        if arguments.len() <= prefix {
            return Ok(value);
        }
        let major = self.force_canonical_major(arguments[prefix])?;
        let (Value::Neutral { head, spine }
        | Value::Whnf { head, spine }
        | Value::Canonical { head, spine }) = self.values[major as usize]
        else {
            return unsupported();
        };
        let (fields, field_count) = self.spine(spine)?;
        let ExprKind::Constant(constructor_name, _) = self
            .expressions
            .get(head, self.budget)?
            .kind(self.expressions, self.levels, self.budget)?
        else {
            return unsupported();
        };
        let constructor = self
            .declarations
            .constructor(
                constructor_name,
                self.scope.before.min(self.declarations.len()),
                self.names,
                self.budget,
            )?
            .ok_or(EvaluationError::Unsupported)?;
        if self
            .names
            .summary(constructor.family, self.budget)?
            .canonical
            != self.names.summary(recursor.family, self.budget)?.canonical
        {
            return unsupported();
        }
        let rule = recursor
            .rules
            .get(constructor.index as usize)
            .ok_or(ResourceError::Invariant)?;
        if self.names.summary(rule.constructor, self.budget)?.canonical
            != self.names.summary(constructor.name, self.budget)?.canonical
            || field_count != recursor.constructor_params as usize + rule.num_fields as usize
        {
            return unsupported();
        }
        let cache_key = if arguments.len() == prefix + 1 {
            let (Value::Neutral { head, .. } | Value::Canonical { head, .. }) =
                self.values[value as usize]
            else {
                return Err(ResourceError::Invariant.into());
            };
            let mut function = self.delayed(head, NONE)?;
            for &argument in &arguments[..prefix] {
                self.force(argument)?;
                // RHS replay still uses this original source certificate.
                function = self.apply(function, argument)?;
            }
            Some((function, major))
        } else {
            None
        };
        if let Some((function, major)) = cache_key
            && let Some(cached) = self.table.get(5, function, major)
        {
            return self.force(cached);
        }
        let rhs = self.declarations.instantiate_nullary_rule_with_cache(
            ConstantUse {
                name,
                arguments: universe,
                parameters: self.scope.parameters,
                before: self.scope.before,
                formation: self.scope.formation,
                mode: self.scope.mode,
                expression_end: self.scope.expression_end,
                level_end: self.scope.level_end,
            },
            constructor.index as usize,
            self.expressions,
            self.levels,
            self.names,
            Some((&mut self.transport, &mut self.transport_budget)),
            self.budget,
        )?;
        let continuation_incoming = self.path;
        self.step()?;
        let mut result = self.delayed(rhs, NONE)?;
        for &argument in &arguments[..prefix] {
            result = self.apply(result, argument)?;
        }
        for &field in &fields[recursor.constructor_params as usize..field_count] {
            result = self.apply(result, field)?;
        }
        for &argument in &arguments[prefix + 1..] {
            result = self.apply(result, argument)?;
        }
        let result = self.force(result)?;
        if let Some((function, major)) = cache_key {
            // Key lookup follows major/key preparation. Retain only the
            // remaining continuation, never the original source's whole path.
            let certificate = self.push_value(Value::Complete {
                head: result,
                height: self.path.height_since(continuation_incoming)?,
            })?;
            self.table
                .insert(5, function, major, certificate, self.budget)?;
        }
        Ok(result)
    }

    fn equal(
        &mut self,
        left: ExprId,
        right: ExprId,
    ) -> Result<Option<ReductionPath>, EvaluationError> {
        let left = self.delayed(left, NONE)?;
        let right = self.delayed(right, NONE)?;
        let mut pairs = Vec::new();
        self.budget.grow_vec(&mut pairs, 1)?;
        pairs.push((left, right, self.path));
        let mut maximum = self.path;
        let result = (|| {
            while let Some((left, right, incoming)) = pairs.pop() {
                self.path = incoming;
                maximum = maximum.maximum(incoming);
                self.budget.charge_work(1)?;
                // One value is equal to itself; forcing it would only replay
                // the same computation on both sides.
                if left == right {
                    continue;
                }
                // Ordered quick check: compare the arguments of two
                // unforced applications of one constant head before any
                // unfolding can force the head (arena perf/args-before-unfold;
                // Courant and Leroy, POPL 2026, section 10). A pair without
                // this shape keeps the forced comparison below; the check
                // never draws a negative conclusion.
                if self.same_head_arguments(left, right, &mut pairs)? {
                    continue;
                }
                let left = self.force(left)?;
                let left_path = self.path;
                self.path = incoming;
                let right = self.force(right);
                self.path = self.path.maximum(left_path);
                maximum = maximum.maximum(self.path);
                let right = right?;
                if left == right {
                    continue;
                }
                let (
                    Value::Neutral {
                        head: a,
                        spine: as_,
                    }
                    | Value::Whnf {
                        head: a,
                        spine: as_,
                    }
                    | Value::Canonical {
                        head: a,
                        spine: as_,
                    },
                    Value::Neutral { head: z, spine: zs }
                    | Value::Whnf { head: z, spine: zs }
                    | Value::Canonical { head: z, spine: zs },
                ) = (self.values[left as usize], self.values[right as usize])
                else {
                    return Ok(None);
                };
                if a != z {
                    let ak = self.expressions.get(a, self.budget)?.kind(
                        self.expressions,
                        self.levels,
                        self.budget,
                    )?;
                    let zk = self.expressions.get(z, self.budget)?.kind(
                        self.expressions,
                        self.levels,
                        self.budget,
                    )?;
                    let (ExprKind::Constant(an, al), ExprKind::Constant(zn, zl)) = (ak, zk) else {
                        return Ok(None);
                    };
                    if al != zl
                        || self.names.summary(an, self.budget)?.canonical
                            != self.names.summary(zn, self.budget)?.canonical
                    {
                        return Ok(None);
                    }
                }
                let (aa, alen) = self.spine(as_)?;
                let (za, zlen) = self.spine(zs)?;
                if alen != zlen {
                    return Ok(None);
                }
                let needed = pairs.len() + alen;
                self.budget.grow_vec(&mut pairs, needed)?;
                for (&a, &z) in aa[..alen].iter().zip(&za[..zlen]) {
                    pairs.push((a, z, self.path));
                }
            }
            Ok(Some(maximum))
        })();
        // Preserve completed producer paths even when another premise fails.
        self.path = self.path.maximum(maximum);
        let cleanup = release(pairs, self.budget);
        if let Err(error) = cleanup {
            return Err(error.into());
        }
        result
    }

    fn retire(mut self) -> Result<(), ResourceError> {
        let errors = [
            release(self.values, self.budget),
            release(self.bindings, self.budget),
            release(self.arguments, self.budget),
            release(self.table.entries, self.budget),
            self.transport
                .retire(&mut self.transport_budget, self.budget),
        ];
        errors.into_iter().find_map(Result::err).map_or(Ok(()), Err)
    }
}

/// Positive-only: both operands are previously checked closed terms. A miss or
/// unsupported fragment grants no verdict, and the ordinary route remains live.
#[allow(clippy::too_many_arguments)]
pub(crate) fn try_equal(
    left: ExprId,
    right: ExprId,
    incoming: ReductionPath,
    scope: Scope<'_>,
    declarations: &Environment,
    expressions: &mut Expressions,
    levels: &mut Levels,
    names: &Names,
    budget: &mut Budget,
    session_force_calls: &mut u32,
) -> Result<Option<ReductionPath>, HeadError> {
    if *session_force_calls >= MAX_FORCE_CALLS {
        return Ok(None);
    }
    if scope.formation.is_some() || scope.mode != Mode::Safe || !scope.parameters.is_empty() {
        return Ok(None);
    }
    let a = expressions.get(left, budget)?;
    let z = expressions.get(right, budget)?;
    if a.loose_range() != 0 || a.has_free() || z.loose_range() != 0 || z.has_free() {
        return Ok(None);
    }
    if !matches!(
        a.kind(expressions, levels, budget)?,
        ExprKind::App(..) | ExprKind::Constant(..) | ExprKind::Let(..)
    ) || !matches!(
        z.kind(expressions, levels, budget)?,
        ExprKind::App(..) | ExprKind::Constant(..) | ExprKind::Let(..)
    ) {
        return Ok(None);
    }
    let depth = a.depth().max(z.depth());
    let limit_override = depth_limit_override();
    if depth > 256 && limit_override.is_none() {
        return std::thread::scope(|scope_thread| {
            let fail_spawn = false;
            let handle = if fail_spawn {
                Err(std::io::Error::other("test-injected thread spawn failure"))
            } else {
                std::thread::Builder::new()
                    .stack_size(64 * 1024 * 1024)
                    .spawn_scoped(scope_thread, move || {
                        try_equal_inner(
                            left,
                            right,
                            incoming,
                            scope,
                            declarations,
                            expressions,
                            levels,
                            names,
                            budget,
                            session_force_calls,
                            MAX_VALUE_DEPTH,
                        )
                    })
            };
            // Thread creation is a backend failure, not an inconclusive
            // comparison. Only the ordinary route's own unsupported result
            // permits a fallback judgment.
            let handle = handle.map_err(|_| HeadError::from(ResourceError::Allocation))?;
            handle
                .join()
                .map_err(|_| HeadError::from(ResourceError::Invariant))?
        });
    }
    try_equal_inner(
        left,
        right,
        incoming,
        scope,
        declarations,
        expressions,
        levels,
        names,
        budget,
        session_force_calls,
        limit_override.unwrap_or(1_024),
    )
}

fn depth_limit_override() -> Option<usize> {
    None
}

#[allow(clippy::too_many_arguments)]
fn try_equal_inner(
    left: ExprId,
    right: ExprId,
    incoming: ReductionPath,
    scope: Scope<'_>,
    declarations: &Environment,
    expressions: &mut Expressions,
    levels: &mut Levels,
    names: &Names,
    budget: &mut Budget,
    session_force_calls: &mut u32,
    depth_limit: usize,
) -> Result<Option<ReductionPath>, HeadError> {
    let mut evaluator = Evaluator {
        scope,
        declarations,
        expressions,
        levels,
        names,
        budget,
        values: Vec::new(),
        bindings: Vec::new(),
        arguments: Vec::new(),
        table: Table::default(),
        transport: super::super::instantiation::Cache::default(),
        transport_budget: SessionCacheBudget::default(),
        path: incoming,
        depth: 0,
        depth_limit,
        force_calls: *session_force_calls,
    };
    let result = evaluator.equal(left, right);
    // Every guarded level releases its depth before returning, on success,
    // unsupported and error alike.
    debug_assert_eq!(evaluator.depth, 0);
    *session_force_calls = evaluator.force_calls;
    let cleanup = evaluator.retire();
    if let Err(error) = cleanup {
        return Err(error.into());
    }
    match result {
        Ok(value) => Ok(value),
        Err(EvaluationError::Unsupported) => Ok(None),
        Err(EvaluationError::Resource(error)) => Err(error.into()),
        Err(EvaluationError::Use(UseError::Unavailable | UseError::UnsafeUse)) => Ok(None),
        Err(EvaluationError::Use(error)) => Err(error.into()),
    }
}
