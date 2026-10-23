//! One resumable head dispatcher. Pausing is not a completed head or a failure.
//! The owner fixes stores, scope and active locals across every advance. The
//! machine owns original/generated syntax handles and scratch; its lifetime is
//! declaration-local.
//! No cache result or installed syntax may retain this machine after retirement.
use super::*;
use crate::syntax::levels::LevelZero;
mod getbang;
mod pending_application;
mod predicate;
mod structure;
mod substitution;

#[derive(Clone, Copy)]
enum Pending {
    None,
    Major(ExprId),
    KPreparing,
    StructurePreparing,
    PredicatePreparing,
    KComparison {
        left: ExprId,
        right: ExprId,
        constructor: ExprId,
    },
}
const _: () = assert!(size_of::<Pending>() == 16);

pub(crate) struct Machine {
    scratch: Scratch,
    expression: ExprId,
    path: ReductionPath,
    failure: Option<HeadError>,
    complete: bool,
    exposure: Exposure,
    pending: Pending,
    /// Unestablished K premise: a K premise comparison of this owner
    /// was abandoned as locally unsupported and ordinary iota resumed on the
    /// original major. Sticky; a completed head is then not an established weak
    /// head and only a positive-only comparison parent may consume it.
    k_unestablished: bool,
}
// 96-byte vector owners plus root/path, pending judgment and sticky state. No imported
// node or declaration entry grows; one current head owns this stack value.
const _: () = assert!(size_of::<Machine>() == 136);

impl Machine {
    /// Recognize the exact whole Bool consumer in this unchanged typed owner.
    /// A saved consumer is authenticated with its transported saturated major;
    /// its original argument is not itself reinterpreted as the visible family.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn finite_candidate(
        &self,
        scope: &Scope<'_>,
        environment: &Environment,
        expressions: &Expressions,
        levels: &Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Option<crate::check::environment::FiniteRequest>, ResourceError> {
        if !environment.finite_available(scope)
            || self.exposure == Exposure::NonDelta
            || self.complete
            || self.failure.is_some()
            || !matches!(self.pending, Pending::None)
            || self.k_unestablished
        {
            return Ok(None);
        }
        let end = self.scratch.applications.len();
        let active = end - self.scratch.base();
        if active == 5 {
            let arguments =
                std::array::from_fn::<_, 5, _>(|i| self.scratch.applications[end - 1 - i].argument);
            return environment.finite_request(
                self.scratch.applications[end - 5].original,
                self.expression,
                &arguments,
                scope,
                expressions,
                levels,
                names,
                b,
            );
        }
        if active != 3 {
            return Ok(None);
        }
        let Some(frame) = self.scratch.iota.last() else {
            return Ok(None);
        };
        if !matches!(frame.kind, Suspension::Iota) || frame.layout()? != (4, 0) || frame.end < 5 {
            return Ok(None);
        }
        let saved_end = frame.end as usize;
        let arguments = std::array::from_fn::<_, 5, _>(|i| {
            self.scratch.applications[saved_end - 1 - i].argument
        });
        let family =
            std::array::from_fn::<_, 3, _>(|i| self.scratch.applications[end - 1 - i].argument);
        let request = environment.finite_request_at(
            self.scratch.applications[saved_end - 5].original,
            frame.recursor,
            &arguments,
            Some((self.expression, family)),
            scope,
            expressions,
            levels,
            names,
            b,
        )?;
        Ok(request.map(|mut request| {
            request.saved_end = frame.end;
            // Native Iota depth is bounded by existing u32 frame limits.
            request.saved_depth = self.scratch.iota.len() as u32;
            request
        }))
    }

    pub(crate) fn finite_incoming(&self) -> ReductionPath {
        self.path
    }

    /// The finite driver consumes only its completed private Bool reply here,
    /// after candidate roots/caches/locals have retired. This owner has stayed
    /// unchanged throughout suspension; a Bool never fills a Decidable-major
    /// slot or resumes a different semantic parent.
    pub(crate) fn resume_finite_bool(
        &mut self,
        source: ExprId,
        saved_end: u32,
        saved_depth: u32,
        result: Head,
        b: &mut Budget,
    ) -> Result<(), HeadError> {
        if self.failure.is_some()
            || self.complete
            || !matches!(self.pending, Pending::None)
            || self.k_unestablished
        {
            return Err(ResourceError::Invariant.into());
        }
        if saved_depth == 0 {
            if saved_end != 0
                || self.scratch.applications.len() - self.scratch.base() != 5
                || self.scratch.applications[self.scratch.base()].original != source
            {
                return Err(ResourceError::Invariant.into());
            }
        } else {
            let frame = *self.scratch.iota.last().ok_or(ResourceError::Invariant)?;
            if self.scratch.iota.len() != saved_depth as usize
                || frame.end != saved_end
                || saved_end < 5
                || !matches!(frame.kind, Suspension::Iota)
                || frame.layout()? != (4, 0)
                || self.scratch.applications.len() != saved_end as usize + 3
                || self.scratch.applications[saved_end as usize - 5].original != source
            {
                return Err(ResourceError::Invariant.into());
            }
            // Retire the transported family spine, then the complete saved Bool
            // consumer. Never resume that consumer with a Bool as its major.
            for _ in 0..3 {
                self.scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
            }
            self.scratch.iota.pop().ok_or(ResourceError::Invariant)?;
            b.release_frames(1)?;
            self.exposure = frame.exposure;
        }
        for _ in 0..5 {
            self.scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
        }
        self.expression = result.expression;
        self.path = result.path;
        Ok(())
    }

    pub(crate) fn new(
        expression: ExprId,
        path: ReductionPath,
        exposure: Exposure,
        b: &mut Budget,
    ) -> Result<Self, HeadError> {
        // Same fixed destruction prepayment as the former local exposure loop.
        b.charge_work(5)?;
        Ok(Self {
            scratch: Scratch::default(),
            expression,
            path,
            failure: None,
            complete: false,
            exposure,
            pending: Pending::None,
            k_unestablished: false,
        })
    }

    /// All continuations stay live on None. In particular the saved application
    /// boundary belongs to this scratch owner, not to the expression table.
    /// An error or caught unwind poisons the machine; a completed head is final.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn advance(
        &mut self,
        scope: &Scope<'_>,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        locals: &LocalContext,
        b: &mut Budget,
    ) -> Result<Option<Head>, HeadError> {
        self.advance_with_cache(
            scope,
            environment,
            expressions,
            levels,
            names,
            locals,
            None,
            b,
        )
    }

    #[allow(clippy::too_many_arguments)]
    #[inline(always)]
    pub(crate) fn advance_with_cache(
        &mut self,
        scope: &Scope<'_>,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        locals: &LocalContext,
        cache: Option<(
            &mut super::super::instantiation::Cache,
            &mut crate::resource::SessionCacheBudget,
        )>,
        b: &mut Budget,
    ) -> Result<Option<Head>, HeadError> {
        self.advance_with_plans(
            scope,
            environment,
            expressions,
            levels,
            names,
            locals,
            cache,
            None,
            b,
        )
    }

    #[allow(clippy::too_many_arguments)]
    #[inline(always)]
    pub(crate) fn advance_with_plans(
        &mut self,
        scope: &Scope<'_>,
        environment: &Environment,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        locals: &LocalContext,
        mut cache: Option<(
            &mut super::super::instantiation::Cache,
            &mut crate::resource::SessionCacheBudget,
        )>,
        mut plans: Option<&mut crate::syntax::expressions::binding::plan::Cache>,
        b: &mut Budget,
    ) -> Result<Option<Head>, HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if self.complete || !matches!(self.pending, Pending::None) {
            let error = ResourceError::Invariant.into();
            self.failure = Some(error);
            return Err(error);
        }
        self.failure = Some(ResourceError::Invariant.into());
        let scratch = &mut self.scratch;
        let mut expression = self.expression;
        let mut path = self.path;
        let mut exposure = self.exposure;
        let result = (|| {
            b.charge_work(1)?;
            b.observe(crate::resource::Event::MachineSteps, 1);
            match expressions
                .get(expression, b)?
                .kind(expressions, levels, b)?
            {
                ExprKind::App(function, argument) => {
                    scratch.push(
                        Application {
                            original: expression,
                            function,
                            argument,
                        },
                        b,
                    )?;
                    expression = function;
                    return Ok(None);
                }
                ExprKind::Let(..) => {
                    let Step::Reduced {
                        expression: next,
                        path: advanced,
                        ..
                    } = expressions.beta_zeta_step(expression, path, levels, names, b)?
                    else {
                        return Err(ResourceError::Invariant.into());
                    };
                    expression = next;
                    path = advanced;
                    return Ok(None);
                }
                ExprKind::Free(id) => {
                    if let Some(value) = locals.get(id, b)?.value() {
                        path = path.after_reduction()?;
                        // Validated local-definition zeta preserves the exact
                        // stored value handle. No copying or inference here.
                        expression = value;
                        b.observe(Event::Reductions, 1);
                        return Ok(None);
                    }
                }
                ExprKind::Constant(name, arguments) => {
                    // Only universe argument scratch crosses mutable transport;
                    // do not clone an expression or uncharged argument vector.
                    b.charge_work(arguments.len() as u64 + 1)?;
                    b.grow_vec(&mut scratch.arguments, arguments.len())?;
                    scratch.arguments.clear();
                    scratch.arguments.extend_from_slice(arguments);
                    let site = ConstantUse {
                        name,
                        arguments: &scratch.arguments,
                        parameters: scope.parameters,
                        before: scope.before,
                        formation: scope.formation,
                        mode: scope.mode,
                        expression_end: scope.expression_end,
                        level_end: scope.level_end,
                    };
                    if exposure == Exposure::Full
                        && scratch.applications.len() - scratch.base() == 4
                        && getbang::root(&site, environment, levels, names, b)?
                    {
                        let end = scratch.applications.len();
                        let index = scratch.applications[end - 4].argument;
                        scratch.suspend(
                            Iota {
                                recursor: expression,
                                end: u32::try_from(end).map_err(|_| ResourceError::Counter)?,
                                payload: SuspensionPayload::Layout {
                                    prefix: 0,
                                    indices: 0,
                                },
                                kind: Suspension::GetBangIndex,
                                exposure,
                            },
                            b,
                        )?;
                        expression = index;
                        return Ok(None);
                    }
                    if exposure == Exposure::Full
                        && scratch.applications.len() - scratch.base() == 2
                    {
                        let end = scratch.applications.len();
                        let left = scratch.applications[end - 1].argument;
                        let right = scratch.applications[end - 2].argument;
                        if let Some(answer) = predicate::literal_step(
                            &site,
                            left,
                            right,
                            path,
                            environment,
                            expressions,
                            levels,
                            names,
                            b,
                        )? {
                            scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
                            scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
                            expression = answer.expression;
                            path = answer.path;
                            return Ok(None);
                        }
                    }
                    if exposure == Exposure::Full
                        && scratch.applications.len() - scratch.base() == 2
                        && (environment
                            .natural_predicate_kind(&site, levels, names, b)?
                            .is_some()
                            || environment
                                .natural_arithmetic_kind(&site, levels, names, b)?
                                .is_some())
                    {
                        let operand = scratch
                            .applications
                            .last()
                            .ok_or(ResourceError::Invariant)?
                            .argument;
                        scratch.suspend(
                            Iota {
                                recursor: expression,
                                end: u32::try_from(scratch.applications.len())
                                    .map_err(|_| ResourceError::Counter)?,
                                payload: SuspensionPayload::Predicate {
                                    incoming: path,
                                    left_height: 0,
                                },
                                kind: Suspension::PredicateLeft,
                                exposure,
                            },
                            b,
                        )?;
                        expression = operand;
                        return Ok(None);
                    }
                    if exposure == Exposure::Full
                        && scratch.arguments.is_empty()
                        && scratch.applications.len() - scratch.base() == 1
                        && let Some((_, _, successor)) = environment.natural_constructors(
                            scope.before,
                            scope.formation,
                            scope.expression_end,
                            expressions,
                            b,
                        )?
                        && names.summary(name, b)?.canonical
                            == names.summary(successor, b)?.canonical
                    {
                        let operand = scratch
                            .applications
                            .last()
                            .ok_or(ResourceError::Invariant)?
                            .argument;
                        scratch.suspend_natural(expression, b)?;
                        expression = operand;
                        return Ok(None);
                    }
                    let step = match exposure {
                        Exposure::Cheap | Exposure::NonDelta => {
                            environment.restricted_head_step(site, levels, names, b)?
                        }
                        Exposure::Full => environment.delta_step_with_cache(
                            site,
                            path,
                            expressions,
                            levels,
                            names,
                            cache
                                .as_mut()
                                .map(|(table, session)| (&mut **table, &mut **session)),
                            b,
                        )?,
                    };
                    match step {
                        DeltaStep::Unfolded {
                            expression: next,
                            path: advanced,
                        } => {
                            expression = next;
                            path = advanced;
                            return Ok(None);
                        }
                        DeltaStep::NoDelta => {}
                        DeltaStep::Quotient(role) => {
                            // Caller invariant: head exposure receives a checked
                            // term/type (possibly transported under matching binders).
                            // check_use validates the constant, not its application.
                            // The checked application supplies parameter consistency
                            // and the lift respectfulness premise without re-inference.
                            // Signature-only staging never grants primitive equations.
                            let committed = environment.lookup(
                                name,
                                scope.before.min(environment.len()),
                                names,
                                b,
                            )?;
                            if !matches!(committed.map(|entry| entry.ty),
                                Some(super::super::TypeSource::Quotient(found)) if found == role)
                            {
                                return Err(HeadError::Unsupported);
                            }
                            let lift = match role {
                                super::super::QuotientRole::Lift => true,
                                super::super::QuotientRole::Induction => false,
                                _ => return Err(ResourceError::Invariant.into()),
                            };
                            let major_position = if lift { 5 } else { 4 };
                            if scratch.applications.len() - scratch.base() > major_position {
                                let major = scratch.applications
                                    [scratch.applications.len() - major_position - 1]
                                    .argument;
                                scratch.suspend_quotient(expression, lift, exposure, b)?;
                                exposure = Exposure::Full;
                                expression = major;
                                return Ok(None);
                            }
                        }
                        DeltaStep::Recursor => {
                            let recursor = environment.recursor(
                                name,
                                scope.before.min(environment.len()),
                                names,
                                b,
                            )?;
                            let Some(recursor) = recursor else {
                                // Private signatures grant typing, not new
                                // equations or a completed stuck-head rule.
                                return Err(HeadError::Unsupported);
                            };
                            let prefix = recursor.common_prefix as usize;
                            let major_position = prefix
                                .checked_add(recursor.num_indices as usize)
                                .ok_or(ResourceError::Counter)?;
                            // Even an empty rule set preserves the demanded major
                            // exposure schedule; absence of equations cannot hide
                            // an unsupported or exhausted major computation.
                            if scratch.applications.len() - scratch.base() > major_position {
                                let major = scratch.applications
                                    [scratch.applications.len() - major_position - 1]
                                    .argument;
                                let next = if recursor.k {
                                    // The atomic inference rules use only a
                                    // checked local domain or installed type.
                                    // Composite majors demand the original checked
                                    // inference judgment with all continuations live.
                                    b.charge_work(1)?;
                                    b.observe(Event::Inferences, 1);
                                    match expressions.get(major, b)?.kind(expressions, levels, b)? {
                                        ExprKind::Free(id) => locals.get(id, b)?.ty(),
                                        ExprKind::Constant(..) => scope.constant_type(
                                            major,
                                            environment,
                                            expressions,
                                            levels,
                                            names,
                                            b,
                                        )?,
                                        _ => {
                                            scratch.suspend_iota(
                                                expression,
                                                prefix,
                                                recursor.num_indices,
                                                true,
                                                exposure,
                                                b,
                                            )?;
                                            exposure = Exposure::Full;
                                            self.pending = Pending::Major(major);
                                            return Ok(None);
                                        }
                                    }
                                } else {
                                    major
                                };
                                scratch.suspend_iota(
                                    expression,
                                    prefix,
                                    recursor.num_indices,
                                    recursor.k,
                                    exposure,
                                    b,
                                )?;
                                exposure = Exposure::Full;
                                expression = next;
                                return Ok(None);
                            }
                        }
                    }
                }
                ExprKind::Bound(_) => return Err(ResourceError::Invariant.into()),
                ExprKind::Projection(family, field, source) => {
                    // Caller established this occurrence's full typing premises.
                    // Committed metadata, not a written structure name or staging,
                    // supplies the computation layout.
                    let metadata = environment
                        .inductive(family, scope.before.min(environment.len()), names, b)?
                        .ok_or(HeadError::Unsupported)?;
                    let [constructor] = metadata.constructors else {
                        return Err(HeadError::Unsupported);
                    };
                    if field >= constructor.num_fields {
                        return Err(HeadError::Unsupported);
                    }
                    let selected = metadata
                        .num_params
                        .checked_add(field)
                        .ok_or(ResourceError::Counter)?;
                    let arity = metadata
                        .num_params
                        .checked_add(constructor.num_fields)
                        .ok_or(ResourceError::Counter)?;
                    scratch.suspend_projection(expression, selected, arity, exposure, b)?;
                    if exposure == Exposure::NonDelta {
                        exposure = Exposure::Full;
                    }
                    expression = source;
                    return Ok(None);
                }
                ExprKind::Sort(_)
                | ExprKind::Lambda(..)
                | ExprKind::Pi(..)
                | ExprKind::Natural(_)
                | ExprKind::String(_) => {}
                // Preserved metadata has no implemented
                // interpretation; demanding its wrapped expression declines
                // instead of inventing one.
                ExprKind::MData(..) => return Err(HeadError::Unsupported),
            }
            // Reassemble neutral applications without re-entering their head
            // search. The stack is outer-to-inner; popping preserves argument
            // order. All function exposure and beta steps share this path.
            'reassemble: loop {
                while scratch.applications.len() > scratch.base() {
                    let frame = scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
                    b.charge_work(1)?;
                    b.observe(crate::resource::Event::MachineSteps, 1);
                    if let ExprKind::Lambda(_, _, body, _) =
                        expressions
                            .get(expression, b)?
                            .kind(expressions, levels, b)?
                    {
                        let advanced = path.after_reduction()?;
                        let reduced = substitution::reduce_with_cache(
                            body,
                            frame.argument,
                            advanced,
                            scratch,
                            expressions,
                            levels,
                            names,
                            match (plans.as_deref_mut(), cache.as_mut()) {
                                (Some(plans), Some((_, session))) => Some((plans, &mut **session)),
                                _ => None,
                            },
                            b,
                        )?;
                        expression = reduced.expression;
                        path = reduced.path;
                        // This beta is performed directly from a completed head;
                        // it does not invoke the immediate beta/zeta helper.
                        b.observe(Event::Reductions, 1);
                        return Ok(None);
                    }
                    expression = if frame.has_original() && expression == frame.function {
                        frame.original
                    } else {
                        expressions.append(
                            ExprKind::App(expression, frame.argument),
                            levels,
                            names,
                            b,
                        )?
                    };
                }
                if let Some(frame) = scratch.iota.pop() {
                    exposure = frame.exposure;
                    b.release_frames(1)?;
                    if matches!(
                        frame.kind,
                        Suspension::Projection | Suspension::Iota | Suspension::IotaNoStructure
                    ) && matches!(
                        expressions
                            .get(expression, b)?
                            .kind(expressions, levels, b)?,
                        ExprKind::String(_)
                    ) {
                        // A literal denotes the certified String.ofList expansion.
                        // Keep the pending eliminator: its head is a definition,
                        // not a constructor ready for projection/iota selection.
                        let expanded = string::expand(
                            expression,
                            path,
                            *scope,
                            environment,
                            expressions,
                            levels,
                            names,
                            b,
                        )?;
                        scratch.suspend(frame, b)?;
                        expression = expanded.expression;
                        path = expanded.path;
                        exposure = Exposure::Full;
                        return Ok(None);
                    }
                    if frame.kind == Suspension::GetBangIndex {
                        let next = getbang::resume(
                            frame,
                            Head { expression, path },
                            scratch,
                            scope,
                            environment,
                            expressions,
                            levels,
                            names,
                            cache
                                .as_mut()
                                .map(|(table, session)| (&mut **table, &mut **session)),
                            b,
                        )?;
                        expression = next.expression;
                        path = next.path;
                        return Ok(None);
                    }
                    if matches!(
                        frame.kind,
                        Suspension::StructureType | Suspension::StructureSort
                    ) {
                        self.pending = Pending::StructurePreparing;
                        // Construction invariant: one sentinel sits exactly above
                        // the no-retry iota boundary. It is never an application
                        // to evaluate, and must retire before ordinary iota resumes.
                        if scratch.applications.len() != frame.end as usize {
                            return Err(ResourceError::Invariant.into());
                        }
                        let mut saved = scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
                        if frame.kind == Suspension::StructureType {
                            if structure::matches_type(
                                expression,
                                frame.recursor,
                                scope,
                                environment,
                                expressions,
                                levels,
                                names,
                                b,
                            )? {
                                saved.argument = expression;
                                scratch.push(saved, b)?;
                                let mut next = frame;
                                next.kind = Suspension::StructureSort;
                                scratch.suspend(next, b)?;
                                self.pending = Pending::Major(expression);
                            } else {
                                expression = saved.original;
                            }
                        } else {
                            let ExprKind::Sort(level) =
                                expressions
                                    .get(expression, b)?
                                    .kind(expressions, levels, b)?
                            else {
                                return Err(HeadError::Unsupported);
                            };
                            // Total decision: both outcomes
                            // are exact normalized-zero observations.
                            expression = match levels.get(level, b)?.zero() {
                                LevelZero::Zero => saved.original,
                                LevelZero::NonZero => structure::expand(
                                    saved.argument,
                                    saved.original,
                                    scratch,
                                    scope,
                                    environment,
                                    expressions,
                                    levels,
                                    names,
                                    b,
                                )?,
                            };
                        }
                        exposure = Exposure::Full;
                        return Ok(None);
                    }
                    if frame.kind == Suspension::IotaNoStructure {
                        self.pending = Pending::StructurePreparing;
                    }
                    if frame.kind == Suspension::Projection {
                        let ExprKind::Projection(family, field, original_source) = expressions
                            .get(frame.recursor, b)?
                            .kind(expressions, levels, b)?
                        else {
                            return Err(ResourceError::Invariant.into());
                        };
                        if !scratch.constructor_arguments.is_empty() {
                            return Err(ResourceError::Invariant.into());
                        }
                        let mut head = expression;
                        loop {
                            b.charge_work(1)?;
                            match expressions.get(head, b)?.kind(expressions, levels, b)? {
                                ExprKind::App(function, argument) => {
                                    let needed = scratch
                                        .constructor_arguments
                                        .len()
                                        .checked_add(1)
                                        .ok_or(ResourceError::Counter)?;
                                    b.grow_vec(&mut scratch.constructor_arguments, needed)?;
                                    scratch.constructor_arguments.push(argument);
                                    head = function;
                                }
                                _ => break,
                            }
                        }
                        let metadata = environment
                            .inductive(family, scope.before.min(environment.len()), names, b)?
                            .ok_or(HeadError::Unsupported)?;
                        let [constructor] = metadata.constructors else {
                            return Err(HeadError::Unsupported);
                        };
                        let matching =
                            match expressions.get(head, b)?.kind(expressions, levels, b)? {
                                ExprKind::Constant(name, _) => {
                                    names.summary(name, b)?.canonical
                                        == names.summary(constructor.constructor, b)?.canonical
                                }
                                _ => false,
                            };
                        if matching {
                            if scratch.constructor_arguments.len() != frame.layout()?.1 as usize
                                || frame.layout()?.0 >= frame.layout()?.1
                            {
                                return Err(HeadError::Unsupported);
                            }
                            let advanced = path.after_reduction()?;
                            expression =
                                scratch.constructor_arguments[scratch.constructor_arguments.len()
                                    - frame.layout()?.0 as usize
                                    - 1];
                            scratch.constructor_arguments.clear();
                            path = advanced;
                            b.observe(Event::Reductions, 1);
                            return Ok(None);
                        }
                        scratch.constructor_arguments.clear();
                        expression = if expression == original_source {
                            frame.recursor
                        } else {
                            expressions.append(
                                ExprKind::Projection(family, field, expression),
                                levels,
                                names,
                                b,
                            )?
                        };
                        // A completed neutral source is stuck, not a new demand
                        // to expose the same projection again.
                        continue 'reassemble;
                    }
                    if matches!(
                        frame.kind,
                        Suspension::QuotientLift | Suspension::QuotientInduction
                    ) {
                        b.charge_work(1)?;
                        b.observe(Event::MachineSteps, 1);
                        let major_position = if frame.kind == Suspension::QuotientLift {
                            5
                        } else {
                            4
                        };
                        let end = frame.end as usize;
                        if scratch.applications.len() != end || end < major_position + 1 {
                            return Err(ResourceError::Invariant.into());
                        }
                        // Only the exact checked mk A r a spine is a quotient redex.
                        // No speculative failure is interpreted as constructor absence.
                        let mut head = expression;
                        let mut representative = None;
                        let mut exact = true;
                        for index in 0..3 {
                            b.charge_work(1)?;
                            match expressions.get(head, b)?.kind(expressions, levels, b)? {
                                ExprKind::App(function, argument) => {
                                    if index == 0 {
                                        representative = Some(argument);
                                    }
                                    head = function;
                                }
                                _ => {
                                    exact = false;
                                    break;
                                }
                            }
                        }
                        if exact {
                            exact = match expressions.get(head, b)?.kind(expressions, levels, b)? {
                                ExprKind::Constant(name, arguments) if arguments.len() == 1 => {
                                    matches!(
                                        environment
                                            .lookup(
                                                name,
                                                scope.before.min(environment.len()),
                                                names,
                                                b
                                            )?
                                            .map(|entry| entry.ty),
                                        Some(super::super::TypeSource::Quotient(
                                            super::super::QuotientRole::Constructor
                                        ))
                                    )
                                }
                                _ => false,
                            };
                        }
                        if exact {
                            let advanced = path.after_reduction()?;
                            let function = scratch.applications[end - 4].argument;
                            let representative = representative.ok_or(ResourceError::Invariant)?;
                            let next = expressions.append(
                                ExprKind::App(function, representative),
                                levels,
                                names,
                                b,
                            )?;
                            for _ in 0..=major_position {
                                scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
                            }
                            expression = next;
                            path = advanced;
                            b.observe(Event::Reductions, 1);
                            return Ok(None);
                        }
                        // Reassemble once, preserving an exposed neutral major and
                        // every trailing argument; do not redispatch this primitive.
                        let major = &mut scratch.applications[end - major_position - 1];
                        if major.argument != expression {
                            if major.has_original() {
                                major.original = expressions.append(
                                    ExprKind::App(major.function, expression),
                                    levels,
                                    names,
                                    b,
                                )?;
                            }
                            major.argument = expression;
                        }
                        expression = frame.recursor;
                        continue 'reassemble;
                    }
                    if matches!(
                        frame.kind,
                        Suspension::PredicateLeft | Suspension::PredicateRight
                    ) {
                        // Keep the observation boundary after popping the frame,
                        // including any failed revalidation or ordinary fallback.
                        self.pending = Pending::PredicatePreparing;
                        let next = predicate::resume(
                            frame,
                            Head { expression, path },
                            scratch,
                            scope,
                            environment,
                            expressions,
                            levels,
                            names,
                            cache
                                .as_mut()
                                .map(|(table, session)| (&mut **table, &mut **session)),
                            b,
                        )?;
                        expression = next.expression;
                        path = next.path;
                        return Ok(None);
                    }
                    if frame.kind == Suspension::Natural {
                        let constructors = environment
                            .natural_constructors(
                                scope.before,
                                scope.formation,
                                scope.expression_end,
                                expressions,
                                b,
                            )?
                            .ok_or(ResourceError::Invariant)?;
                        let operand =
                            expressions
                                .get(expression, b)?
                                .kind(expressions, levels, b)?;
                        let bytes = match operand {
                            ExprKind::Natural(bytes) => Some(bytes),
                            ExprKind::Constant(name, [])
                                if names.summary(name, b)?.canonical
                                    == names.summary(constructors.1, b)?.canonical =>
                            {
                                Some(&b"0"[..])
                            }
                            _ => None,
                        };
                        if let Some(bytes) = bytes {
                            let advanced = path.after_reduction()?;
                            let digits =
                                crate::check::natural::successor(bytes, b).map_err(|error| {
                                    match error {
                                        crate::check::natural::Error::Resource(error) => {
                                            HeadError::from(error)
                                        }
                                        crate::check::natural::Error::Unsupported => {
                                            HeadError::Unsupported
                                        }
                                    }
                                })?;
                            let appended = expressions.append(
                                ExprKind::Natural(digits.as_bytes()),
                                levels,
                                names,
                                b,
                            );
                            let retired = digits.retire(b);
                            if let Some(error) = full::select_failure([
                                appended.as_ref().err().copied().map(HeadError::from),
                                retired.err().map(HeadError::from),
                                None,
                                None,
                            ]) {
                                return Err(error);
                            }
                            expression = appended.map_err(HeadError::from)?;
                            scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
                            path = advanced;
                            b.observe(Event::Reductions, 1);
                            return Ok(None);
                        }
                        // Completed nonnumeric exposure makes acceleration
                        // inapplicable. Rebuild this constructor without re-entering
                        // the same successor head and looping on a neutral operand.
                        let application = scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
                        expression =
                            if application.has_original() && expression == application.argument {
                                application.original
                            } else {
                                expressions.append(
                                    ExprKind::App(frame.recursor, expression),
                                    levels,
                                    names,
                                    b,
                                )?
                            };
                        // Reassembly may now return to an enclosing suspension.
                        // The complete constructor spine is already head-exposed.
                        continue 'reassemble;
                    }
                    if frame.kind == Suspension::K {
                        self.pending = Pending::KPreparing;
                        let ExprKind::Constant(rec_name, _) = expressions
                            .get(frame.recursor, b)?
                            .kind(expressions, levels, b)?
                        else {
                            return Err(ResourceError::Invariant.into());
                        };
                        let recursor = environment
                            .recursor(rec_name, scope.before.min(environment.len()), names, b)?
                            .ok_or(ResourceError::Invariant)?;
                        if recursor.constructor_params != 0 || recursor.num_indices != 0 {
                            // This recursor was resolved below the committed
                            // frontier, even in a live signature-staging phase.
                            // Its own validated K metadata is the only authority;
                            // the new group contributes no computation rule.
                            let (constructor, right) = prepare_k(
                                expression,
                                recursor,
                                scratch,
                                scope,
                                environment,
                                expressions,
                                levels,
                                names,
                                b,
                            )?;
                            // Keep the original eliminator frame while comparison
                            // runs. On either completed answer, or after the driver
                            // abandons an unestablished premise, ordinary iota
                            // resumes once; this frame must never dispatch K again.
                            let mut ordinary = frame;
                            ordinary.kind = Suspension::Iota;
                            scratch.suspend(ordinary, b)?;
                            self.pending = Pending::KComparison {
                                left: expression,
                                right,
                                constructor,
                            };
                            return Ok(None);
                        }
                        let ExprKind::Constant(family, arguments) = expressions
                            .get(expression, b)?
                            .kind(expressions, levels, b)?
                        else {
                            return Err(HeadError::Unsupported);
                        };
                        b.charge_work(arguments.len() as u64 + 1)?;
                        b.grow_vec(&mut scratch.arguments, arguments.len())?;
                        scratch.arguments.clear();
                        scratch.arguments.extend_from_slice(arguments);
                        let ExprKind::Constant(name, _) = expressions
                            .get(frame.recursor, b)?
                            .kind(expressions, levels, b)?
                        else {
                            return Err(ResourceError::Invariant.into());
                        };
                        let recursor = environment
                            .recursor(name, scope.before.min(environment.len()), names, b)?
                            .ok_or(ResourceError::Invariant)?;
                        if !recursor.k || recursor.rules.len() != 1 {
                            return Err(ResourceError::Invariant.into());
                        }
                        if names.summary(family, b)?.canonical
                            != names.summary(recursor.family, b)?.canonical
                        {
                            return Err(HeadError::Unsupported);
                        }
                        let constructor = expressions.append(
                            ExprKind::Constant(recursor.rules[0].constructor, &scratch.arguments),
                            levels,
                            names,
                            b,
                        )?;
                        b.observe(Event::Inferences, 1);
                        let ty = scope.constant_type(
                            constructor,
                            environment,
                            expressions,
                            levels,
                            names,
                            b,
                        )?;
                        // Validator invariant: this nullary constructor's exact
                        // type is its bare family applied to the same universe
                        // parameter vector. Substitution returns the exact
                        // replacement handles. This completed
                        // structural comparison supplies the positive K premise;
                        // no mismatched/unimplemented route supplies a negative.
                        let ExprKind::Constant(candidate_family, arguments) =
                            expressions.get(ty, b)?.kind(expressions, levels, b)?
                        else {
                            return Err(ResourceError::Invariant.into());
                        };
                        if arguments != scratch.arguments
                            || names.summary(candidate_family, b)?.canonical
                                != names.summary(family, b)?.canonical
                        {
                            return Err(HeadError::Unsupported);
                        }
                        expression = constructor;
                        self.pending = Pending::None;
                    }
                    if frame.kind == Suspension::Iota {
                        self.pending = Pending::StructurePreparing;
                        if structure::eligible(
                            expression,
                            frame.recursor,
                            scope,
                            environment,
                            expressions,
                            levels,
                            names,
                            b,
                        )? {
                            let mut ordinary = frame;
                            ordinary.kind = Suspension::IotaNoStructure;
                            scratch.suspend(ordinary, b)?;
                            scratch.push(
                                Application {
                                    original: expression,
                                    function: expression,
                                    argument: expression,
                                },
                                b,
                            )?;
                            scratch.suspend(
                                Iota {
                                    recursor: frame.recursor,
                                    end: u32::try_from(scratch.applications.len())
                                        .map_err(|_| ResourceError::Counter)?,
                                    payload: SuspensionPayload::Layout {
                                        prefix: 0,
                                        indices: 0,
                                    },
                                    kind: Suspension::StructureType,
                                    exposure: Exposure::Full,
                                },
                                b,
                            )?;
                            self.pending = Pending::Major(expression);
                            exposure = Exposure::Full;
                            return Ok(None);
                        }
                        self.pending = Pending::None;
                    }
                    let mut constructor_head = expression;
                    scratch.constructor_arguments.clear();
                    // Construction premise: the validator checked original raw
                    // uniform parameters and the caller supplied a checked major.
                    // Its constructor parameters can therefore be discarded;
                    // the rule receives the recursor's already checked parameters
                    // and the actual constructor fields, in telescope order.
                    // This does not assert equality for arbitrary supplied terms.
                    let constructor = loop {
                        b.charge_work(1)?;
                        match expressions
                            .get(constructor_head, b)?
                            .kind(expressions, levels, b)?
                        {
                            ExprKind::App(function, argument) => {
                                let needed = scratch
                                    .constructor_arguments
                                    .len()
                                    .checked_add(1)
                                    .ok_or(ResourceError::Counter)?;
                                b.grow_vec(&mut scratch.constructor_arguments, needed)?;
                                scratch.constructor_arguments.push(argument);
                                constructor_head = function;
                            }
                            ExprKind::Constant(name, _) => break name,
                            ExprKind::Natural(bytes)
                                if scratch.constructor_arguments.is_empty() =>
                            {
                                let (family, zero, successor) = environment
                                    .natural_constructors(
                                        scope.before,
                                        scope.formation,
                                        scope.expression_end,
                                        expressions,
                                        b,
                                    )?
                                    .ok_or(HeadError::Unsupported)?;
                                let ExprKind::Constant(recursor_name, _) = expressions
                                    .get(frame.recursor, b)?
                                    .kind(expressions, levels, b)?
                                else {
                                    return Err(ResourceError::Invariant.into());
                                };
                                let recursor = environment
                                    .recursor(
                                        recursor_name,
                                        scope.before.min(environment.len()),
                                        names,
                                        b,
                                    )?
                                    .ok_or(HeadError::Unsupported)?;
                                if names.summary(recursor.family, b)?.canonical
                                    != names.summary(family, b)?.canonical
                                {
                                    return Err(HeadError::Unsupported);
                                }
                                // One demanded constructor layer, fed directly to
                                // the checked iota rule. Redispatching a generated
                                // successor head here would immediately accelerate
                                // it back to the same literal.
                                let advanced = path.after_reduction()?;
                                let constructor = if bytes == b"0" {
                                    zero
                                } else {
                                    let digits = crate::check::natural::predecessor(bytes, b)
                                        .map_err(|error| match error {
                                            crate::check::natural::Error::Resource(error) => {
                                                HeadError::from(error)
                                            }
                                            crate::check::natural::Error::Unsupported => {
                                                HeadError::Unsupported
                                            }
                                        })?;
                                    let appended = expressions.append(
                                        ExprKind::Natural(digits.as_bytes()),
                                        levels,
                                        names,
                                        b,
                                    );
                                    let retired = digits.retire(b);
                                    if let Some(error) = full::select_failure([
                                        appended.as_ref().err().copied().map(HeadError::from),
                                        retired.err().map(HeadError::from),
                                        None,
                                        None,
                                    ]) {
                                        return Err(error);
                                    }
                                    b.grow_vec(&mut scratch.constructor_arguments, 1)?;
                                    scratch
                                        .constructor_arguments
                                        .push(appended.map_err(HeadError::from)?);
                                    successor
                                };
                                path = advanced;
                                b.observe(Event::Reductions, 1);
                                break constructor;
                            }
                            ExprKind::Free(_) | ExprKind::Projection(..) => {
                                expression = rebuild_stuck_recursor(
                                    frame,
                                    expression,
                                    scratch,
                                    expressions,
                                    levels,
                                    names,
                                    b,
                                )?;
                                continue 'reassemble;
                            }
                            // Other representations still require their own completed
                            // applicability rules, notably string literal conversion.
                            _ => return Err(HeadError::Unsupported),
                        }
                    };
                    let Some(constructor) = environment.constructor(
                        constructor,
                        scope.before.min(environment.len()),
                        names,
                        b,
                    )?
                    else {
                        expression = rebuild_stuck_recursor(
                            frame,
                            expression,
                            scratch,
                            expressions,
                            levels,
                            names,
                            b,
                        )?;
                        continue 'reassemble;
                    };
                    let ExprKind::Constant(name, args) =
                        expressions
                            .get(frame.recursor, b)?
                            .kind(expressions, levels, b)?
                    else {
                        return Err(ResourceError::Invariant.into());
                    };
                    b.charge_work(args.len() as u64 + 1)?;
                    b.grow_vec(&mut scratch.arguments, args.len())?;
                    scratch.arguments.clear();
                    scratch.arguments.extend_from_slice(args);
                    let recursor = environment
                        .recursor(name, scope.before.min(environment.len()), names, b)?
                        .ok_or(ResourceError::Invariant)?;
                    if names.summary(recursor.family, b)?.canonical
                        != names.summary(constructor.family, b)?.canonical
                    {
                        return Err(HeadError::Unsupported);
                    }
                    let rule = recursor
                        .rules
                        .get(constructor.index as usize)
                        .ok_or(ResourceError::Invariant)?;
                    let arity = (recursor.constructor_params as usize)
                        .checked_add(rule.num_fields as usize)
                        .ok_or(ResourceError::Counter)?;
                    if scratch.constructor_arguments.len() != arity {
                        return Err(HeadError::Unsupported);
                    }
                    if names.summary(rule.constructor, b)?.canonical
                        != names.summary(constructor.name, b)?.canonical
                    {
                        return Err(ResourceError::Invariant.into());
                    }
                    let advanced = path.after_reduction()?;
                    expression = environment.instantiate_nullary_rule_with_cache(
                        ConstantUse {
                            name,
                            arguments: &scratch.arguments,
                            parameters: scope.parameters,
                            before: scope.before,
                            formation: scope.formation,
                            mode: scope.mode,
                            expression_end: scope.expression_end,
                            level_end: scope.level_end,
                        },
                        constructor.index as usize,
                        expressions,
                        levels,
                        names,
                        cache
                            .as_mut()
                            .map(|(table, session)| (&mut **table, &mut **session)),
                        b,
                    )?;
                    // Queue the same applications without transient expression nodes.
                    // Ordinary beta exposure still consumes every exported RHS binder.
                    pending_application::after_iota(
                        scratch,
                        frame,
                        expression,
                        rule.num_fields as usize,
                        b,
                    )?;
                    path = advanced;
                    b.observe(Event::Reductions, 1);
                    let prefix = frame.layout()?.0 as usize;
                    if scope.formation.is_none()
                        && (1..=8).contains(&prefix)
                        && let Some((table, session)) = cache.as_mut()
                    {
                        let end = scratch.applications.len();
                        let start = end.checked_sub(prefix).ok_or(ResourceError::Invariant)?;
                        if start < scratch.base() {
                            return Err(ResourceError::Invariant.into());
                        }
                        // after_iota put the fixed prefix at the top, in nearest
                        // binder order. Constructor fields remain below it.
                        let mut arguments = [expression; 8];
                        for (argument, frame) in
                            arguments.iter_mut().zip(&scratch.applications[start..])
                        {
                            *argument = frame.argument;
                        }
                        if let Some((result, completed_path)) = table.reduce_rule_prefix(
                            expression,
                            &arguments[..prefix],
                            path,
                            expressions,
                            levels,
                            names,
                            session,
                            b,
                        )? {
                            b.charge_work(prefix as u64 + 1)?;
                            b.release_frames(prefix)?;
                            scratch.applications.truncate(start);
                            expression = result;
                            path = completed_path;
                        }
                    }
                    return Ok(None);
                }
                return Ok(Some(Head { expression, path }));
            }
        })();
        self.expression = expression;
        self.path = path;
        self.exposure = exposure;
        if result.is_ok()
            && matches!(
                self.pending,
                Pending::StructurePreparing | Pending::PredicatePreparing
            )
        {
            self.pending = Pending::None;
        }
        self.failure = result.as_ref().err().copied();
        self.complete = matches!(result, Ok(Some(_)));
        result
    }

    /// Only the ordinary checking driver can service this demand. Auxiliary
    /// synchronous routes must return Unsupported, never a provisional head.
    pub(crate) fn major_request(&self) -> Option<TypeObservation> {
        match self.pending {
            Pending::Major(root) => Some(TypeObservation {
                root,
                incoming: self.path,
            }),
            _ => None,
        }
    }

    pub(crate) fn comparison_request(&self) -> Option<(ExprId, ExprId, ReductionPath)> {
        match self.pending {
            Pending::KComparison { left, right, .. } => Some((left, right, self.path)),
            _ => None,
        }
    }

    pub(crate) fn observing_type(&self) -> bool {
        !matches!(self.pending, Pending::None)
            || self.scratch.iota.iter().any(|frame| {
                matches!(
                    frame.kind,
                    Suspension::K
                        | Suspension::PredicateLeft
                        | Suspension::PredicateRight
                        | Suspension::StructureType
                        | Suspension::StructureSort
                        | Suspension::IotaNoStructure
                )
            })
    }

    pub(crate) fn resume_comparison(
        &mut self,
        decision: full::comparison::Decision,
    ) -> Result<(), HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        self.failure = Some(ResourceError::Invariant.into());
        let Pending::KComparison { constructor, .. } = self.pending else {
            return Err(ResourceError::Invariant.into());
        };
        if self.complete {
            return Err(ResourceError::Invariant.into());
        }
        self.expression = match decision {
            full::comparison::Decision::Equal(path) => {
                path.height_since(self.path)?;
                self.path = path;
                constructor
            }
            full::comparison::Decision::Different(_) => self.original_major()?,
        };
        self.exposure = Exposure::Full;
        self.pending = Pending::None;
        self.failure = None;
        Ok(())
    }

    /// Major of the suspended K frame, which resume has already turned into
    /// the ordinary iota frame kept on top while the premise runs.
    fn original_major(&self) -> Result<ExprId, HeadError> {
        let frame = self.scratch.iota.last().ok_or(ResourceError::Invariant)?;
        let (prefix, indices) = frame.layout()?;
        let position = (frame.end as usize)
            .checked_sub(prefix as usize)
            .and_then(|n| n.checked_sub(indices as usize))
            .and_then(|n| n.checked_sub(1))
            .ok_or(ResourceError::Invariant)?;
        Ok(self
            .scratch
            .applications
            .get(position)
            .ok_or(ResourceError::Invariant)?
            .argument)
    }

    /// True only while this live owner waits for its own K premise comparison.
    pub(crate) fn k_premise_pending(&self) -> bool {
        matches!(self.pending, Pending::KComparison { .. })
            && self.failure.is_none()
            && !self.complete
    }

    pub(crate) fn k_unestablished(&self) -> bool {
        self.k_unestablished
    }

    /// Unestablished K premise. The driver has retired the premise
    /// comparison after a locally unsupported result and has already made this
    /// owner's only consumer positive-only. K is not performed: the original
    /// major resumes the kept ordinary iota frame exactly as after a completed
    /// Different, with no path certificate. Resource, internal and cleanup
    /// failures never reach this call; they stay terminal in the driver.
    pub(crate) fn resume_unestablished_k(&mut self) -> Result<(), HeadError> {
        if !self.k_premise_pending() {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        self.failure = Some(ResourceError::Invariant.into());
        self.expression = self.original_major()?;
        self.exposure = Exposure::Full;
        self.pending = Pending::None;
        self.k_unestablished = true;
        self.failure = None;
        Ok(())
    }

    pub(crate) fn resume_major(
        &mut self,
        ty: ExprId,
        path: ReductionPath,
    ) -> Result<(), HeadError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        if self.complete || !matches!(self.pending, Pending::Major(_)) {
            self.failure = Some(ResourceError::Invariant.into());
            return Err(ResourceError::Invariant.into());
        }
        if let Err(error) = path.height_since(self.path) {
            self.failure = Some(error.into());
            return Err(error.into());
        }
        self.pending = Pending::None;
        self.expression = ty;
        self.path = path;
        Ok(())
    }

    /// Abandon only locally unsupported optional work. All cleanup and other
    /// operation failures remain terminal; no completed result is returned.
    pub(crate) fn abandon(mut self, b: &mut Budget) -> Result<(), HeadError> {
        if self.failure == Some(HeadError::Unsupported) {
            self.failure = None;
        }
        self.retire(b)
    }

    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), HeadError> {
        let cleanup = self.scratch.retire(b).err().map(HeadError::from);
        match full::select_failure([self.failure, cleanup, None, None]) {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

/// Derive typing of the constructor candidate from the checked major type's
/// parameters and the validated family/constructor parameter correspondence.
/// Substitution follows the original instantiated constructor telescope; it does
/// not re-check transported domains or grant authority to unchecked syntax.
#[allow(clippy::too_many_arguments)]
fn prepare_k(
    actual: ExprId,
    recursor: crate::check::environment::nullary::RecursorView<'_>,
    scratch: &mut Scratch,
    scope: &Scope<'_>,
    environment: &Environment,
    expressions: &mut Expressions,
    levels: &mut Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<(ExprId, ExprId), HeadError> {
    if !recursor.k || recursor.rules.len() != 1 || recursor.rules[0].num_fields != 0 {
        return Err(ResourceError::Invariant.into());
    }
    scratch.constructor_arguments.clear();
    let mut head = actual;
    while let ExprKind::App(function, argument) =
        expressions.get(head, b)?.kind(expressions, levels, b)?
    {
        let needed = scratch
            .constructor_arguments
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        b.grow_vec(&mut scratch.constructor_arguments, needed)?;
        scratch.constructor_arguments.push(argument);
        head = function;
    }
    let ExprKind::Constant(family, universes) =
        expressions.get(head, b)?.kind(expressions, levels, b)?
    else {
        return Err(HeadError::Unsupported);
    };
    if names.summary(family, b)?.canonical != names.summary(recursor.family, b)?.canonical {
        return Err(HeadError::Unsupported);
    }
    let required = (recursor.constructor_params as usize)
        .checked_add(recursor.num_indices as usize)
        .ok_or(ResourceError::Counter)?;
    if scratch.constructor_arguments.len() != required {
        return Err(HeadError::Unsupported);
    }
    b.charge_work(universes.len() as u64 + 1)?;
    b.grow_vec(&mut scratch.arguments, universes.len())?;
    scratch.arguments.clear();
    scratch.arguments.extend_from_slice(universes);
    let mut constructor = expressions.append(
        ExprKind::Constant(recursor.rules[0].constructor, &scratch.arguments),
        levels,
        names,
        b,
    )?;
    let mut ty = scope.constant_type(constructor, environment, expressions, levels, names, b)?;
    for &argument in scratch
        .constructor_arguments
        .iter()
        .rev()
        .take(recursor.constructor_params as usize)
    {
        let ExprKind::Pi(_, _, body, _) = expressions.get(ty, b)?.kind(expressions, levels, b)?
        else {
            return Err(ResourceError::Invariant.into());
        };
        ty = expressions.bind(body, 0, Binding::Instantiate(&[argument]), levels, names, b)?;
        constructor = expressions.append(ExprKind::App(constructor, argument), levels, names, b)?;
    }
    scratch.constructor_arguments.clear();
    Ok((constructor, ty))
}

/// All major observations and optional K/structure conversions have completed.
/// This only reconstructs a checked neutral head; it grants no negative judgment.
fn rebuild_stuck_recursor(
    frame: Iota,
    major: ExprId,
    scratch: &mut Scratch,
    expressions: &mut Expressions,
    levels: &Levels,
    names: &Names,
    b: &mut Budget,
) -> Result<ExprId, HeadError> {
    let mut result = frame.recursor;
    for _ in 0..u64::from(frame.layout()?.0) + u64::from(frame.layout()?.1) {
        let saved = scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
        // Immutable original applications already represent an unchanged spine.
        // Reallocating them would manufacture progress for exact-handle head
        // comparisons even though no reduction occurred. This is reconstruction
        // within this head owner, not interning or cached conversion evidence.
        result = if saved.has_original() && result == saved.function {
            saved.original
        } else {
            expressions.append(ExprKind::App(result, saved.argument), levels, names, b)?
        };
    }
    let saved = scratch.pop(b)?.ok_or(ResourceError::Invariant)?;
    scratch.constructor_arguments.clear();
    if saved.has_original() && result == saved.function && major == saved.argument {
        Ok(saved.original)
    } else {
        Ok(expressions.append(ExprKind::App(result, major), levels, names, b)?)
    }
}
