//! Checked functional-recursive specialization. All handles are owner-local.
use super::*;
use crate::check::environment::CheckednessMint;
use crate::syntax::expressions::binding::Binding;
use crate::syntax::levels::{LevelId, LevelZero};
use crate::syntax::local_context::{CheckedTy, FreeId};
mod templates;
pub(super) use templates::{ConstructorInput, FamilyInput, Templates};

#[derive(Clone, Copy)]
pub(super) struct Binder {
    id: FreeId,
    expression: ExprId,
    ty: ExprId,
    generated_ty: ExprId,
    path: ReductionPath,
}
#[derive(Clone, Copy)]
struct Field {
    binder: Binder,
    /// The total identically-zero decision on this field's sort
    /// Zero marks a proof field, NonZero a data field.
    prop: LevelZero,
    recursive: u32, // zero: nonrecursive; otherwise target family position + 1
    indices: FieldSpan,
    telescope: FieldSpan,
}
struct RecursiveField {
    family: u32,
    indices: Option<FieldSpan>,
    telescope: FieldSpan,
    path: ReductionPath,
}
#[derive(Clone, Copy)]
struct FieldSpan {
    start: u32,
    len: u32,
}
const _: () = assert!(std::mem::size_of::<Binder>() == 20);
const _: () = assert!(std::mem::size_of::<Field>() == 44);
const _: () = assert!(std::mem::size_of::<FieldSpan>() == 8);
#[derive(Clone, Copy)]
struct FamilyTelescope {
    name: NameId,
    recursor: NameId,
    indices: FieldSpan,
    result: LevelId,
    constructors: FieldSpan,
    results: u32,
}
const _: () = assert!(std::mem::size_of::<FamilyTelescope>() == 32);

#[derive(Default)]
pub(super) struct Scratch {
    binders: Vec<Binder>,
    families: Vec<FamilyTelescope>,
    family_set: families::FamilySet,
    universes: Vec<LevelId>,
    constructors: Vec<ExprId>,
    results: Vec<ExprId>,
    fields: Vec<Field>,
    field_spans: Vec<FieldSpan>,
    recursive_indices: Vec<ExprId>,
    recursive_binders: Vec<Binder>,
    elimination: Option<LevelId>,
    pub recursive: bool,
    pub reflexive: bool,
    pub large_fields: bool,
    pub parameters: usize,
    pub indices: usize,
    pub result: Option<LevelId>,
}
// Nine flat buffers, two optional levels and scalar telescope summaries.
const _: () = assert!(std::mem::size_of::<Scratch>() == 280);
pub(super) fn push<T>(work: &mut Working<'_>, v: &mut Vec<T>, x: T) -> Result<(), Stop> {
    let n = v.len().checked_add(1).ok_or(ResourceError::Counter)?;
    work.budget.grow_vec(v, n)?;
    v.push(x);
    Ok(())
}
pub(super) fn apply(work: &mut Working<'_>, mut f: ExprId, xs: &[ExprId]) -> Result<ExprId, Stop> {
    for &x in xs {
        f = append(work, ExprKind::App(f, x))?;
    }
    Ok(f)
}
fn kind<'a>(work: &'a mut Working<'_>, expression: ExprId) -> Result<ExprKind<'a>, Stop> {
    Ok(work.expressions.get(expression, work.budget)?.kind(
        work.expressions,
        work.levels,
        work.budget,
    )?)
}
fn substitute(work: &mut Working<'_>, body: ExprId, replacement: ExprId) -> Result<ExprId, Stop> {
    Ok(work.expressions.bind(
        body,
        0,
        Binding::Instantiate(&[replacement]),
        work.levels,
        work.names,
        work.budget,
    )?)
}
fn binder(work: &mut Working<'_>, ty: ExprId, path: ReductionPath) -> Result<Binder, Stop> {
    let id = work.context.enter_checked(
        // Certificate authority: scheme construction operates on types the
        // ordinary field-classification rules checked in this same scope.
        CheckedTy::checked(ty, CheckednessMint::mint()),
        None,
        NameId::ANONYMOUS,
        BinderInfo::Default,
        work.expressions,
        work.names,
        work.budget,
    )?;
    let expression = append(work, ExprKind::Free(id.slot()))?;
    Ok(Binder {
        id,
        expression,
        ty,
        generated_ty: ty,
        path,
    })
}
fn close(
    work: &mut Working<'_>,
    body: ExprId,
    binders: &[Binder],
    lambda: bool,
) -> Result<ExprId, Stop> {
    close_by(work, body, binders.len(), |k| binders[k], lambda)
}
/// Closes `body` over the telescope `binder(0..n)`, outermost first, with one
/// abstraction pass over the body and one over each binder type that has free
/// variables. `ids[i]` becomes `Bound(i)`, so the body sees binder `n - 1` as 0
/// and binder `k`'s type sees binder `k - 1` as 0 through binder 0 as `k - 1`:
/// the same term as closing one binder at a time from the innermost, without
/// rewriting the growing body once per binder. Binder ids are distinct
/// (`binder` enters each one fresh); a repeat is an invariant failure in
/// `bind`, never a verdict.
fn close_by(
    work: &mut Working<'_>,
    mut body: ExprId,
    n: usize,
    binder: impl Fn(usize) -> Binder,
    lambda: bool,
) -> Result<ExprId, Stop> {
    if n == 0 {
        return Ok(body);
    }
    let mut ids: Vec<u32> = Vec::new();
    work.budget.grow_vec(&mut ids, n)?;
    ids.extend((0..n).rev().map(|k| binder(k).id.slot()));
    let result = (|| {
        body = work.expressions.bind(
            body,
            0,
            Binding::Abstract(&ids),
            work.levels,
            work.names,
            work.budget,
        )?;
        for k in (0..n).rev() {
            let mut ty = binder(k).generated_ty;
            if k != 0 && work.expressions.get(ty, work.budget)?.has_free() {
                ty = work.expressions.bind(
                    ty,
                    0,
                    Binding::Abstract(&ids[n - k..]),
                    work.levels,
                    work.names,
                    work.budget,
                )?;
            }
            body = append(
                work,
                if lambda {
                    ExprKind::Lambda(NameId::ANONYMOUS, ty, body, BinderInfo::Default)
                } else {
                    ExprKind::Pi(NameId::ANONYMOUS, ty, body, BinderInfo::Default)
                },
            )?;
        }
        Ok::<_, Stop>(body)
    })();
    let bytes = ids.capacity() * std::mem::size_of::<u32>();
    drop(ids);
    work.budget.release(bytes as u64)?;
    result
}
fn application_binders(
    work: &mut Working<'_>,
    mut f: ExprId,
    binders: &[Binder],
) -> Result<ExprId, Stop> {
    for b in binders {
        f = append(work, ExprKind::App(f, b.expression))?;
    }
    Ok(f)
}
impl Scratch {
    pub(super) fn retire(mut self, work: &mut Working<'_>, success: bool) -> Result<(), Stop> {
        // Allocation order is family parameters/indices, all constructor fields,
        // then motive/minors. Every successful exit leaves that order in reverse.
        let base = (self.parameters + self.indices).min(self.binders.len());
        let leave: Result<(), ResourceError> = if success {
            (|| {
                for binder in self.binders[base..].iter().rev() {
                    work.context.leave(binder.id, work.budget)?;
                }
                // A completed nonpositive result may stop within a field's
                // telescope, before a Field row exists. Its suffix still owns
                // live locals and precedes every completed field on retirement.
                let assigned = self.fields.last().map_or(0, |field| {
                    field.telescope.start as usize + field.telescope.len as usize
                });
                for binder in self.recursive_binders[assigned..].iter().rev() {
                    work.context.leave(binder.id, work.budget)?;
                }
                for field in self.fields.iter().rev() {
                    work.context.leave(field.binder.id, work.budget)?;
                    let span = field.telescope;
                    for binder in self.recursive_binders
                        [span.start as usize..span.start as usize + span.len as usize]
                        .iter()
                        .rev()
                    {
                        work.context.leave(binder.id, work.budget)?;
                    }
                }
                for binder in self.binders[..base].iter().rev() {
                    work.context.leave(binder.id, work.budget)?;
                }
                Ok(())
            })()
        } else {
            Ok(())
        };
        let bytes = self.binders.capacity() * std::mem::size_of::<Binder>()
            + self.families.capacity() * std::mem::size_of::<FamilyTelescope>()
            + self.universes.capacity() * 4
            + self.constructors.capacity() * 4
            + self.results.capacity() * 4
            + self.fields.capacity() * std::mem::size_of::<Field>()
            + self.field_spans.capacity() * std::mem::size_of::<FieldSpan>()
            + self.recursive_indices.capacity() * 4
            + self.recursive_binders.capacity() * std::mem::size_of::<Binder>();
        let family_set = std::mem::take(&mut self.family_set);
        drop(self);
        let membership = family_set.retire(work.budget);
        let release = work.budget.release(bytes as u64);
        membership?;
        release?;
        leave?;
        Ok(())
    }
    pub(super) fn family<T: Templates>(
        &mut self,
        work: &mut Working<'_>,
        request: &T,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<(), Stop> {
        self.family_set.fill(work, request.family_names())?;
        let first = request.family(0)?;
        self.parameters = first.num_params as usize;
        let parameters = first.parameters;
        // One raw parameter node per block universe, shared by every generated
        // family/constructor application in this owner. No interning.
        for &name in parameters {
            let level = work
                .levels
                .append(LevelKind::Param(name), work.names, work.budget)?;
            push(work, &mut self.universes, level)?;
        }
        for member in 0..request.family_count() {
            let family = request.family(member)?;
            if family.num_params != first.num_params
                || !parameters_equal(work.names, parameters, family.parameters, work.budget)?
            {
                return Err(Stop::Judgment(
                    crate::decode::primitive_decode::ordinary_session::Negative::TypeMismatch,
                ));
            }
            // The initial caller uses the prior environment; subsequent staging
            // passes repeat these already checked roots without new authority.
            work.check_root_scope(parameters, &[family.ty])?;
            let mut path =
                work.check_type(family.ty, false, ReductionPath::start(), scope, environment)?;
            let mut current = family.ty;
            let mut position = 0usize;
            let index_start = if member == 0 {
                self.parameters
            } else {
                self.binders.len()
            };
            let result;
            loop {
                let head = work.expose_checked(current, path, scope, environment)?;
                path = head.path;
                match kind(work, head.expression)? {
                    ExprKind::Pi(_, domain, body, _) => {
                        path = work.check_type(domain, false, path, scope, environment)?;
                        let generated_ty = generated_domain(work, environment, domain)?;
                        let local = if member != 0 && position < self.parameters {
                            let common = self.binders[position];
                            path = work.compare_checked_types(
                                domain,
                                common.ty,
                                path.maximum(common.path),
                                scope,
                                environment,
                            )?;
                            common
                        } else {
                            let mut local = binder(work, domain, path)?;
                            local.generated_ty = generated_ty;
                            push(work, &mut self.binders, local)?;
                            local
                        };
                        current = substitute(work, body, local.expression)?;
                        position = position.checked_add(1).ok_or(ResourceError::Counter)?;
                    }
                    ExprKind::Sort(level) => {
                        result = level;
                        break;
                    }
                    _ => {
                        if let NeutralFamily::Proven =
                            completed_neutral_family(head, work, scope, environment)?
                        {
                            return Err(Stop::Judgment(crate::decode::primitive_decode::ordinary_session::Negative::ExpectedSort));
                        }
                        return Err(Stop::Unsupported);
                    }
                }
            }
            let indices = position.checked_sub(self.parameters).ok_or(Stop::Judgment(
                crate::decode::primitive_decode::ordinary_session::Negative::ExpectedPi,
            ))?;
            if let Some(first) = self.families.first() {
                // U is the ordered positive admission comparison. An unavailable
                // or non-equal result supplies no general universe inequality.
                let equal = work.levels.with_helpers(work.names, work.budget, |h| {
                    h.compare_universes(result, first.result)
                })?;
                if equal != crate::syntax::levels::UniverseComparison::Equal {
                    return Err(Stop::Unsupported);
                }
            } else {
                self.result = Some(result);
            }
            self.indices = self
                .indices
                .checked_add(indices)
                .ok_or(ResourceError::Counter)?;
            push(
                work,
                &mut self.families,
                FamilyTelescope {
                    name: family.name,
                    recursor: NameId::ANONYMOUS,
                    indices: FieldSpan {
                        start: u32::try_from(index_start).map_err(|_| ResourceError::Counter)?,
                        len: u32::try_from(indices).map_err(|_| ResourceError::Counter)?,
                    },
                    result,
                    constructors: FieldSpan { start: 0, len: 0 },
                    results: 0,
                },
            )?;
        }
        for index in 0..request.recursor_count() {
            let name = request.recursor_name(index, work)?;
            let Some((family, Component::String("rec"))) = work.names.view(name, work.budget)?
            else {
                continue;
            };
            if let Some(member) = self.family_set.find(family, work.names, work.budget)? {
                if self.families[member].recursor != NameId::ANONYMOUS {
                    return Err(ResourceError::Invariant.into());
                }
                self.families[member].recursor = name;
            }
        }
        Ok(())
    }
    // Only independently generated, structurally family-owned names enter here.
    // Assigning an owner-local name supplies no environment computation authority.
    pub(super) fn set_recursor(
        &mut self,
        work: &mut Working<'_>,
        family: NameId,
        name: NameId,
    ) -> Result<(), Stop> {
        let Some((owner, Component::String("rec"))) = work.names.view(name, work.budget)? else {
            return Err(ResourceError::Invariant.into());
        };
        if !same(work.names, owner, family, work.budget)? {
            return Err(ResourceError::Invariant.into());
        }
        let member = self
            .family_set
            .find(family, work.names, work.budget)?
            .ok_or(ResourceError::Invariant)?;
        if self.families[member].recursor != NameId::ANONYMOUS {
            return Err(ResourceError::Invariant.into());
        }
        self.families[member].recursor = name;
        Ok(())
    }
    pub(super) fn family_indices(&self, member: usize) -> Result<u32, ResourceError> {
        self.families
            .get(member)
            .map(|f| f.indices.len)
            .ok_or(ResourceError::Invariant)
    }
    #[allow(
        clippy::let_and_return,
        reason = "test-only observer omitted from public source"
    )]
    pub(super) fn constructors<T: Templates>(
        &mut self,
        work: &mut Working<'_>,
        request: &T,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<bool, Stop> {
        self.large_fields = true;
        for member in 0..request.family_count() {
            let family = request.family(member)?;
            let result_level = self.families[member].result;
            let indices = self.families[member].indices.len as usize;
            let constructor_start = self.constructors.len();
            self.families[member].results =
                u32::try_from(self.results.len()).map_err(|_| ResourceError::Counter)?;
            for index in 0..family.constructors {
                let constructor = request.constructor(member, index, work)?;
                let mut current = constructor.ty;
                let mut path =
                    work.check_type(current, false, ReductionPath::start(), scope, environment)?;
                for parameter in &self.binders[..self.parameters] {
                    // Constructor prefixes are syntactic, never erased by WHNF.
                    let ExprKind::Pi(_, domain, body, _) = kind(work, current)? else {
                        return Err(Stop::Unsupported);
                    };
                    let domain_path = work.check_type(domain, false, path, scope, environment)?;
                    generated_domain(work, environment, domain)?;
                    // Both domains have been checked before positive comparison.
                    let incoming = domain_path.maximum(parameter.path);
                    let height = work.with_normalization(scope, environment, |session| {
                        if session.structurally_identical(domain, parameter.ty)? {
                            Ok(0)
                        } else {
                            let result = session
                                .compare(domain, incoming, parameter.ty, incoming)
                                .map(|(a, b)| a.height.max(b.height));
                            result
                        }
                    })?;
                    path = incoming.after_height(height)?;
                    current = substitute(work, body, parameter.expression)?;
                }
                let field_start = self.fields.len();
                while let ExprKind::Pi(_, domain, body, _) = kind(work, current)? {
                    // isReflexive observes the syntactic opened field domain before
                    // WHNF, independently of recursive-argument classification.
                    if matches!(kind(work, domain)?, ExprKind::Pi(..))
                        && !no_block(work, domain, &self.family_set)?
                    {
                        self.reflexive = true;
                    }
                    // The raw pass established original uniformity. Keep the original
                    // opened domain in the local; WHNF is only for classification.
                    let sort = if let Some(sort) =
                        work.try_formation_sort(domain, scope, environment)?
                    {
                        // Independently bounded positive engine; incoming
                        // ordinary path is preserved, not reset or synthesized.
                        sort
                    } else {
                        let inferred = work.infer_at(domain, path, scope, environment)?;
                        let head =
                            work.expose_checked(inferred.ty, inferred.path, scope, environment)?;
                        let ExprKind::Sort(sort) = kind(work, head.expression)? else {
                            return Err(Stop::Unsupported);
                        };
                        path = head.path;
                        sort
                    };
                    // Ordered D OR Z: interruption of D cannot select the Z branch.
                    // Total decision: NonZero declines; it
                    // asserts no positivity of anything.
                    if !work.levels.with_helpers(work.names, work.budget, |h| {
                        h.dominates(result_level, sort)
                    })? && work.levels.get(result_level, work.budget)?.zero() != LevelZero::Zero
                    {
                        return Ok(false);
                    }
                    let generated_ty = generated_domain(work, environment, domain)?;
                    let prop = work.levels.get(sort, work.budget)?.zero();
                    let exposed = work.expose_checked(domain, path, scope, environment)?;
                    let Some(classified) = self.recursive_field(
                        work,
                        exposed.expression,
                        exposed.path,
                        scope,
                        environment,
                    )?
                    else {
                        return Ok(false);
                    };
                    let recursive = classified.indices;
                    let telescope = classified.telescope;
                    path = classified.path;
                    self.recursive |= recursive.is_some();
                    let mut local = binder(work, domain, path)?;
                    local.generated_ty = generated_ty;
                    push(
                        work,
                        &mut self.fields,
                        Field {
                            binder: local,
                            prop,
                            recursive: if recursive.is_some() {
                                classified.family
                            } else {
                                0
                            },
                            indices: recursive.unwrap_or(FieldSpan { start: 0, len: 0 }),
                            telescope,
                        },
                    )?;
                    current = substitute(work, body, local.expression)?;
                }
                let span = FieldSpan {
                    start: u32::try_from(field_start).map_err(|_| ResourceError::Counter)?,
                    len: u32::try_from(self.fields.len() - field_start)
                        .map_err(|_| ResourceError::Counter)?,
                };
                push(work, &mut self.field_spans, span)?;
                let mut arguments = Vec::new();
                let parsed = (|| {
                    let mut head = current;
                    loop {
                        match work.expressions.get(head, work.budget)?.kind(
                            work.expressions,
                            work.levels,
                            work.budget,
                        )? {
                            ExprKind::App(f, a) => {
                                push(work, &mut arguments, a)?;
                                head = f;
                            }
                            ExprKind::Constant(name, us) => {
                                if !same(work.names, name, family.name, work.budget)?
                                    || us.len() != self.universes.len()
                                {
                                    return Err(Stop::Unsupported);
                                };
                                break;
                            }
                            _ => return Err(Stop::Unsupported),
                        }
                    }
                    arguments.reverse();
                    if arguments.len() != self.parameters + indices {
                        return Err(Stop::Unsupported);
                    };
                    if work
                        .try_formation_sort(current, scope, environment)?
                        .is_none()
                    {
                        work.infer_at(current, path, scope, environment)?;
                    }
                    for &index in &arguments[self.parameters..] {
                        push(work, &mut self.results, index)?;
                    }
                    let constructor =
                        append(work, ExprKind::Constant(constructor.name, &self.universes))?;
                    let mut constructor =
                        application_binders(work, constructor, &self.binders[..self.parameters])?;
                    for field in &self.fields[field_start..] {
                        constructor =
                            append(work, ExprKind::App(constructor, field.binder.expression))?;
                        if field.prop == LevelZero::NonZero {
                            let mut exact_argument = false;
                            for &argument in &arguments {
                                work.budget.charge_work(1)?;
                                if matches!(kind(work, argument)?, ExprKind::Free(id) if id == field.binder.id.slot())
                                {
                                    exact_argument = true;
                                    break;
                                }
                            }
                            self.large_fields &= exact_argument;
                        }
                    }
                    push(work, &mut self.constructors, constructor)?;
                    Ok(())
                })();
                let bytes = arguments.capacity() * 4;
                drop(arguments);
                work.budget.release(bytes as u64)?;
                parsed?;
            }
            self.families[member].constructors = FieldSpan {
                start: u32::try_from(constructor_start).map_err(|_| ResourceError::Counter)?,
                len: u32::try_from(self.constructors.len() - constructor_start)
                    .map_err(|_| ResourceError::Counter)?,
            };
        }
        Ok(true)
    }
    // Follow only family-free Pi domains of the fully checked field type.
    // Inner locals remain owned by this field until generated IH/RHS closing;
    // no imported root can mention these fresh identities. Flat spans preserve
    // dependent index arguments without copying a telescope for each use.
    fn recursive_field(
        &mut self,
        work: &mut Working<'_>,
        root: ExprId,
        mut path: ReductionPath,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<Option<RecursiveField>, Stop> {
        let start =
            u32::try_from(self.recursive_binders.len()).map_err(|_| ResourceError::Counter)?;
        if no_block(work, root, &self.family_set)? {
            return Ok(Some(RecursiveField {
                family: 0,
                indices: None,
                telescope: FieldSpan { start, len: 0 },
                path,
            }));
        }
        let original = root;
        let mut root = root;
        while let ExprKind::Pi(_, domain, body, _) = kind(work, root)? {
            path = work.check_type(domain, false, path, scope, environment)?;
            let exposed = work.expose_checked(domain, path, scope, environment)?;
            path = exposed.path;
            if !no_block(work, exposed.expression, &self.family_set)? {
                return Ok(None);
            }
            let generated_ty = generated_domain(work, environment, domain)?;
            let mut local = binder(work, domain, path)?;
            local.generated_ty = generated_ty;
            push(work, &mut self.recursive_binders, local)?;
            let opened = substitute(work, body, local.expression)?;
            let head = work.expose_checked(opened, path, scope, environment)?;
            path = head.path;
            root = head.expression;
        }
        let telescope = FieldSpan {
            start,
            len: u32::try_from(self.recursive_binders.len())
                .map_err(|_| ResourceError::Counter)?
                .checked_sub(start)
                .ok_or(ResourceError::Invariant)?,
        };
        // Exposure of an inner codomain can discard an earlier occurrence.
        // Classify the returned terminal, never the original field as a proxy.
        if root != original && no_block(work, root, &self.family_set)? {
            return Ok(Some(RecursiveField {
                family: 0,
                indices: None,
                telescope,
                path,
            }));
        }
        let mut args = Vec::new();
        let result = (|| {
            let mut current = root;
            let member;
            loop {
                match kind(work, current)? {
                    ExprKind::App(f, a) => {
                        push(work, &mut args, a)?;
                        current = f;
                    }
                    ExprKind::Constant(name, us) => {
                        let universe_count = us.len();
                        let target = self.family_set.find(name, work.names, work.budget)?;
                        if target.is_none() {
                            // The field and every demanded observation have been
                            // checked, and root is their completed WHNF terminal.
                            // A remaining family occurrence beneath a committed
                            // recursor is not strictly positive. Unlike a nested
                            // type former, this head has no nested translation.
                            // Missing metadata supplies no negative evidence.
                            if environment
                                .recursor(
                                    name,
                                    scope.before.min(environment.len()),
                                    work.names,
                                    work.budget,
                                )?
                                .is_some()
                            {
                                return Ok(None);
                            }
                            return Err(Stop::Unsupported);
                        }
                        member = target.ok_or(ResourceError::Invariant)?;
                        if universe_count != self.universes.len() {
                            return Err(Stop::Unsupported);
                        }
                        break;
                    }
                    _ => return Err(Stop::Unsupported),
                }
            }
            args.reverse();
            let index_count = self.families[member].indices.len as usize;
            if args.len() != self.parameters + index_count {
                return Err(Stop::Unsupported);
            }
            for (&arg, parameter) in args[..self.parameters].iter().zip(&self.binders) {
                if !matches!(kind(work, arg)?, ExprKind::Free(id) if id == parameter.id.slot()) {
                    return Err(Stop::Unsupported);
                }
            }
            let start =
                u32::try_from(self.recursive_indices.len()).map_err(|_| ResourceError::Counter)?;
            for &index in &args[self.parameters..] {
                if !no_block(work, index, &self.family_set)? {
                    return Err(Stop::Unsupported);
                }
                push(work, &mut self.recursive_indices, index)?;
            }
            Ok(Some((
                u32::try_from(member)
                    .map_err(|_| ResourceError::Counter)?
                    .checked_add(1)
                    .ok_or(ResourceError::Counter)?,
                FieldSpan {
                    start,
                    len: u32::try_from(index_count).map_err(|_| ResourceError::Counter)?,
                },
            )))
        })();
        let bytes = args.capacity() * 4;
        drop(args);
        work.budget.release(bytes as u64)?;
        result.map(|indices| {
            indices.map(|(family, indices)| RecursiveField {
                family,
                indices: Some(indices),
                telescope,
                path,
            })
        })
    }
    fn recursive_arguments(&self, field: &Field) -> Result<&[ExprId], Stop> {
        let span = field.indices;
        self.recursive_indices
            .get(span.start as usize..span.start as usize + span.len as usize)
            .ok_or_else(|| ResourceError::Invariant.into())
    }
    fn functional_binders(&self, field: &Field) -> Result<&[Binder], Stop> {
        let span = field.telescope;
        self.recursive_binders
            .get(span.start as usize..span.start as usize + span.len as usize)
            .ok_or_else(|| ResourceError::Invariant.into())
    }
    pub(super) fn field_count(&self, index: usize) -> Result<u32, Stop> {
        Ok(self
            .field_spans
            .get(index)
            .ok_or(ResourceError::Invariant)?
            .len)
    }
    fn fields(&self, index: usize) -> Result<&[Field], Stop> {
        let span = self
            .field_spans
            .get(index)
            .ok_or(ResourceError::Invariant)?;
        self.fields
            .get(span.start as usize..span.start as usize + span.len as usize)
            .ok_or_else(|| ResourceError::Invariant.into())
    }
    fn close_fields(
        &self,
        work: &mut Working<'_>,
        body: ExprId,
        index: usize,
        lambda: bool,
    ) -> Result<ExprId, Stop> {
        let fields = self.fields(index)?;
        close_by(work, body, fields.len(), |k| fields[k].binder, lambda)
    }
    /// Closes `body` over the parameters, then the motives and minors, then
    /// `inner(0..m)`, in one `close_by` pass.
    fn close_rule(
        &self,
        work: &mut Working<'_>,
        body: ExprId,
        m: usize,
        inner: impl Fn(usize) -> Binder,
        lambda: bool,
    ) -> Result<ExprId, Stop> {
        let p = self.parameters;
        let base = p + self.indices;
        let outer = p + (self.binders.len() - base);
        let binder = |k: usize| {
            if k < p {
                self.binders[k]
            } else if k < outer {
                self.binders[base + k - p]
            } else {
                inner(k - outer)
            }
        };
        close_by(work, body, outer + m, binder, lambda)
    }
    fn family_application(&self, work: &mut Working<'_>, name: NameId) -> Result<ExprId, Stop> {
        let member = self
            .family_set
            .find(name, work.names, work.budget)?
            .ok_or(ResourceError::Invariant)?;
        let indices = self.families[member].indices;
        let f = append(work, ExprKind::Constant(name, &self.universes))?;
        let f = application_binders(work, f, &self.binders[..self.parameters])?;
        application_binders(
            work,
            f,
            &self.binders[indices.start as usize..indices.start as usize + indices.len as usize],
        )
    }
    fn constructor_member(&self, index: usize) -> Result<usize, Stop> {
        let member = self.families.partition_point(|family| {
            family.constructors.start as usize + family.constructors.len as usize <= index
        });
        let family = self.families.get(member).ok_or(ResourceError::Invariant)?;
        if index < family.constructors.start as usize {
            return Err(ResourceError::Invariant.into());
        }
        Ok(member)
    }
    fn constructor_results(&self, index: usize) -> Result<&[ExprId], Stop> {
        let member = self.constructor_member(index)?;
        let family = self.families[member];
        let width = family.indices.len as usize;
        let start = family.results as usize + (index - family.constructors.start as usize) * width;
        self.results
            .get(start..start + width)
            .ok_or_else(|| ResourceError::Invariant.into())
    }
    pub(super) fn add_motives(
        &mut self,
        work: &mut Working<'_>,
        universe: Option<NameId>,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<(), Stop> {
        let v = match universe {
            Some(name) => work
                .levels
                .append(LevelKind::Param(name), work.names, work.budget)?,
            None => LevelId::ZERO,
        };
        self.elimination = universe.map(|_| v);
        let sort = append(work, ExprKind::Sort(v))?;
        let base = self.parameters + self.indices;
        // All motives precede all minors, in specification order. A recursive
        // field's target position selects its motive, never its owner's motive.
        for member in 0..self.families.len() {
            let family = self.families[member];
            let major = self.family_application(work, family.name)?;
            let motive = append(
                work,
                ExprKind::Pi(NameId::ANONYMOUS, major, sort, BinderInfo::Default),
            )?;
            let indices = family.indices;
            let motive = close(
                work,
                motive,
                &self.binders
                    [indices.start as usize..indices.start as usize + indices.len as usize],
                false,
            )?;
            let path =
                work.check_type(motive, false, ReductionPath::start(), scope, environment)?;
            let motive = binder(work, motive, path)?;
            push(work, &mut self.binders, motive)?;
        }
        for (index, &constructor) in self.constructors.iter().enumerate() {
            let member = self.constructor_member(index)?;
            let result = apply(
                work,
                self.binders[base + member].expression,
                self.constructor_results(index)?,
            )?;
            let mut result = append(work, ExprKind::App(result, constructor))?;
            // Hypotheses follow all original fields. Their domains never depend
            // on another hypothesis, so no temporary IH locals are needed.
            for field in self
                .fields(index)?
                .iter()
                .rev()
                .filter(|field| field.recursive != 0)
            {
                let target = field.recursive as usize - 1;
                let hypothesis = apply(
                    work,
                    self.binders[base + target].expression,
                    self.recursive_arguments(field)?,
                )?;
                let inner = self.functional_binders(field)?;
                let value = application_binders(work, field.binder.expression, inner)?;
                let hypothesis = append(work, ExprKind::App(hypothesis, value))?;
                let hypothesis = close(work, hypothesis, inner, false)?;
                result = append(
                    work,
                    ExprKind::Pi(NameId::ANONYMOUS, hypothesis, result, BinderInfo::Default),
                )?;
            }
            let result = self.close_fields(work, result, index, false)?;
            let path =
                work.check_type(result, false, ReductionPath::start(), scope, environment)?;
            let minor = binder(work, result, path)?;
            push(work, &mut self.binders, minor)?;
        }
        Ok(())
    }
    pub(super) fn recursor(&self, work: &mut Working<'_>, name: NameId) -> Result<ExprId, Stop> {
        let member = self
            .family_set
            .find(name, work.names, work.budget)?
            .ok_or(ResourceError::Invariant)?;
        let family = self.families[member];
        let base = self.parameters + self.indices;
        let indices = &self.binders[family.indices.start as usize
            ..family.indices.start as usize + family.indices.len as usize];
        let result = application_binders(work, self.binders[base + member].expression, indices)?;
        let major = append(work, ExprKind::Bound(0))?;
        let result = append(work, ExprKind::App(result, major))?;
        let ty = self.family_application(work, name)?;
        let result = append(
            work,
            ExprKind::Pi(NameId::ANONYMOUS, ty, result, BinderInfo::Default),
        )?;
        self.close_rule(work, result, indices.len(), |k| indices[k], false)
    }
    pub(super) fn rhs(
        &self,
        work: &mut Working<'_>,
        recursor: NameId,
        index: usize,
    ) -> Result<ExprId, Stop> {
        let member = self.constructor_member(index)?;
        if !same(
            work.names,
            recursor,
            self.families[member].recursor,
            work.budget,
        )? {
            return Err(ResourceError::Invariant.into());
        }
        let base = self.parameters + self.indices;
        let mut body = self.binders[base + self.families.len() + index].expression;
        for field in self.fields(index)? {
            body = append(work, ExprKind::App(body, field.binder.expression))?;
        }
        if self.fields(index)?.iter().any(|field| field.recursive != 0) {
            let mut universes = Vec::new();
            // Scope: this one RHS, fixed checked block and locals. Only completed
            // syntactic prefixes are shared; these are not cached rule templates.
            let mut prefixes: Vec<Option<ExprId>> = Vec::new();
            let result = (|| {
                if let Some(level) = self.elimination {
                    push(work, &mut universes, level)?;
                }
                for &level in &self.universes {
                    push(work, &mut universes, level)?;
                }
                work.budget.grow_vec(&mut prefixes, self.families.len())?;
                prefixes.resize(self.families.len(), None);
                for field in self
                    .fields(index)?
                    .iter()
                    .filter(|field| field.recursive != 0)
                {
                    let target = field.recursive as usize - 1;
                    let prefix = if let Some(prefix) = prefixes[target] {
                        prefix
                    } else {
                        let name = self.families[target].recursor;
                        if name == NameId::ANONYMOUS {
                            return Err(ResourceError::Invariant.into());
                        }
                        let constant = append(work, ExprKind::Constant(name, &universes))?;
                        let prefix =
                            application_binders(work, constant, &self.binders[..self.parameters])?;
                        let prefix = application_binders(work, prefix, &self.binders[base..])?;
                        prefixes[target] = Some(prefix);
                        prefix
                    };
                    let call = apply(work, prefix, self.recursive_arguments(field)?)?;
                    let inner = self.functional_binders(field)?;
                    let value = application_binders(work, field.binder.expression, inner)?;
                    let call = append(work, ExprKind::App(call, value))?;
                    let call = close(work, call, inner, true)?;
                    body = append(work, ExprKind::App(body, call))?;
                }
                Ok::<_, Stop>(())
            })();
            let bytes = universes.capacity() * 4
                + prefixes.capacity() * std::mem::size_of::<Option<ExprId>>();
            drop(universes);
            drop(prefixes);
            work.budget.release(bytes as u64)?;
            result?;
        }
        let fields = self.fields(index)?;
        self.close_rule(work, body, fields.len(), |k| fields[k].binder, true)
    }
    /// Closed type of an owned generated rule; checked independently before
    /// restoration, then restored alongside its RHS for public rechecking.
    pub(super) fn rule_type(&self, work: &mut Working<'_>, index: usize) -> Result<ExprId, Stop> {
        let base = self.parameters + self.indices;
        let member = self.constructor_member(index)?;
        let result = apply(
            work,
            self.binders[base + member].expression,
            self.constructor_results(index)?,
        )?;
        let result = append(work, ExprKind::App(result, self.constructors[index]))?;
        let fields = self.fields(index)?;
        self.close_rule(work, result, fields.len(), |k| fields[k].binder, false)
    }
    pub(super) fn recheck(
        &self,
        work: &mut Working<'_>,
        rhs: ExprId,
        index: usize,
        scope: Scope<'_>,
        environment: &Environment,
    ) -> Result<(), Stop> {
        let base = self.parameters + self.indices;
        let applied = application_binders(work, rhs, &self.binders[..self.parameters])?;
        let mut applied = application_binders(work, applied, &self.binders[base..])?;
        for field in self.fields(index)? {
            applied = append(work, ExprKind::App(applied, field.binder.expression))?;
        }
        let member = self.constructor_member(index)?;
        let expected = apply(
            work,
            self.binders[base + member].expression,
            self.constructor_results(index)?,
        )?;
        let expected = append(work, ExprKind::App(expected, self.constructors[index]))?;
        // Exact exported schema matching remains separate. This internal typed
        // check uses conversion only after expected itself has checked Sort.
        // No required artifact pass is omitted, and failure proves nothing.
        if work.check_formation_rule(applied, expected, scope, environment)? {
            return Ok(());
        }
        let actual = work.infer_at(applied, ReductionPath::start(), scope, environment)?;
        if !matches(work, actual.ty, expected)? {
            return Err(ResourceError::Invariant.into());
        }
        Ok(())
    }
}

pub(super) use crate::check::environment::validation::schema_match::matches;

/// One-sided classification: NotProven grants no shape or verdict evidence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NeutralFamily {
    Proven,
    NotProven,
}

/// Called only after checked exported-family typing and completed full exposure.
/// An active non-let major and committed exactly saturated recursor remain neutral
/// only after the head owner's K/major/structure obligations completed. No failed
/// route, raw application shape or private signature supplies that premise.
pub(super) fn completed_neutral_family(
    head: crate::check::environment::normalization::Head,
    work: &mut Working<'_>,
    scope: Scope<'_>,
    environment: &Environment,
) -> Result<NeutralFamily, Stop> {
    let ExprKind::App(_, major) = kind(work, head.expression)? else {
        return Ok(NeutralFamily::NotProven);
    };
    let ExprKind::Free(local) = kind(work, major)? else {
        return Ok(NeutralFamily::NotProven);
    };
    if work.context.get(local, work.budget)?.value().is_some() {
        return Ok(NeutralFamily::NotProven);
    }
    let mut root = head.expression;
    let mut arguments = 0usize;
    while let ExprKind::App(function, _) = kind(work, root)? {
        work.budget.charge_work(1)?;
        arguments = arguments.checked_add(1).ok_or(ResourceError::Counter)?;
        root = function;
    }
    let ExprKind::Constant(name, _) = kind(work, root)? else {
        return Ok(NeutralFamily::NotProven);
    };
    let Some(recursor) = environment.recursor(
        name,
        scope.before.min(environment.len()),
        work.names,
        work.budget,
    )?
    else {
        return Ok(NeutralFamily::NotProven);
    };
    let arity = (recursor.common_prefix as usize)
        .checked_add(recursor.num_indices as usize)
        .and_then(|n| n.checked_add(1))
        .ok_or(ResourceError::Counter)?;
    Ok(if arguments == arity {
        NeutralFamily::Proven
    } else {
        NeutralFamily::NotProven
    })
}
