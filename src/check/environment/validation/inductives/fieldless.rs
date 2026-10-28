//! One safe family with nonrecursive or supported functional recursive fields and parameters/indices.
use super::*;
use crate::check::environment::{Environment, Formation, NullaryMetadata, NullaryRule};
use crate::decode::primitive_decode::inductives::Inductive;
use crate::syntax::levels::{LevelPositive, LevelZero};
mod families;
mod memo;
mod mutual;
mod nested;
const _: () = assert!(std::mem::size_of::<(ExprId, bool)>() == 8);
const _: () = assert!(std::mem::size_of::<(ExprId, u32, bool)>() == 12);
mod scheme;

#[cfg(feature = "introspection")]
fn capture_work(
    work: &mut Working<'_>,
    declaration: NameId,
    rules: &[crate::report::failure_snapshot::Rule],
    identities: &[crate::report::failure_snapshot::Identity],
) {
    use crate::check::diagnostic::Sources;
    use crate::report::failure_snapshot::{Capture, Snapshot};
    if work
        .budget
        .failure_snapshot()
        .is_some_and(crate::report::failure_snapshot::Snapshot::has_rules)
    {
        return;
    }
    let snapshot = Snapshot::capture(Capture {
        declaration: Some(declaration),
        rules,
        identities,
        invariant: None,
        delayed: None,
        mismatch: None,
        sources: Sources {
            expressions: work.expressions,
            levels: work.levels,
            names: work.names,
            locals: Some(work.context),
        },
    });
    work.budget.capture_failure(snapshot);
}

fn parameters_equal(
    names: &Names,
    a: &[NameId],
    b: &[NameId],
    budget: &mut Budget,
) -> Result<bool, ResourceError> {
    if a.len() != b.len() {
        return Ok(false);
    }
    budget.charge_work(a.len() as u64 + 1)?;
    for (&a, &b) in a.iter().zip(b) {
        if !same(names, a, b, budget)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn with_scratch<T>(
    work: &mut Working<'_>,
    f: impl FnOnce(&mut Working<'_>, &mut scheme::Scratch) -> Result<T, Stop>,
) -> Result<T, Stop> {
    let mut scratch = scheme::Scratch::default();
    let result = f(work, &mut scratch);
    scratch.retire(work, result.is_ok())?;
    result
}
fn fresh_index(
    names: &Names,
    name: NameId,
    b: &mut Budget,
) -> Result<Option<usize>, ResourceError> {
    let Some((prefix, Component::String(text))) = names.view(name, b)? else {
        return Ok(None);
    };
    if !same(names, prefix, NameId::ANONYMOUS, b)? {
        return Ok(None);
    }
    b.charge_work(text.len() as u64 + 1)?;
    if text == "u" {
        return Ok(Some(0));
    }
    let Some(digits) = text.strip_prefix("u_") else {
        return Ok(None);
    };
    if digits.is_empty() || digits.starts_with('0') {
        return Ok(None);
    }
    Ok(digits.bytes().try_fold(0usize, |n, c| {
        if c.is_ascii_digit() {
            n.checked_mul(10)?.checked_add(usize::from(c - b'0'))
        } else {
            None
        }
    }))
}
fn fresh_parameter(
    names: &Names,
    parameters: &[NameId],
    candidate: NameId,
    b: &mut Budget,
) -> Result<bool, ResourceError> {
    let Some(index) = fresh_index(names, candidate, b)? else {
        return Ok(false);
    };
    if index > parameters.len() {
        return Ok(false);
    }
    for n in 0..=index {
        let mut found = false;
        for &p in parameters {
            b.charge_work(1)?;
            found |= fresh_index(names, p, b)? == Some(n);
        }
        if !found {
            return Ok(n == index);
        }
    }
    Ok(false)
}
fn raw_kind<'a>(work: &'a mut Working<'_>, id: ExprId) -> Result<ExprKind<'a>, Stop> {
    Ok(work
        .expressions
        .get(id, work.budget)?
        .kind(work.expressions, work.levels, work.budget)?)
}
// Only the generated binder domain changes. Raw syntax has already undergone
// occurrence/uniformity traversal, and ordinary checking inspects every argument.
// A wrapped recursive occurrence unsupported by that raw pass still declines.
fn generated_domain(
    work: &mut Working<'_>,
    environment: &Environment,
    mut domain: ExprId,
) -> Result<ExprId, Stop> {
    loop {
        let mut head = domain;
        let mut first = None;
        let mut arguments = 0usize;
        while let ExprKind::App(function, argument) = raw_kind(work, head)? {
            arguments = arguments.checked_add(1).ok_or(ResourceError::Counter)?;
            first = Some(argument);
            head = function;
        }
        let ExprKind::Constant(name, _) = raw_kind(work, head)? else {
            return Ok(domain);
        };
        let Some((slot, arity)) =
            crate::check::environment::annotations::annotation(name, work.names, work.budget)?
        else {
            return Ok(domain);
        };
        if arguments != arity {
            return Ok(domain);
        }
        // Syntax support is checked through ordinary declaration validation; no
        // annotation name, including autoParam, bypasses the identity certificate.
        if !environment.certified_annotation(
            name,
            slot,
            environment.len(),
            work.names,
            work.budget,
        )? {
            return Err(Stop::Unsupported);
        }
        domain = first.ok_or(ResourceError::Invariant)?;
    }
}
fn no_block(
    work: &mut Working<'_>,
    root: ExprId,
    families: &families::FamilySet,
) -> Result<bool, Stop> {
    no_matching_family(work, root, |name, names, budget| {
        Ok(families.find(name, names, budget)?.is_some())
    })
}
fn no_matching_family(
    work: &mut Working<'_>,
    root: ExprId,
    member: impl Fn(NameId, &Names, &mut Budget) -> Result<bool, ResourceError>,
) -> Result<bool, Stop> {
    let mut todo = Vec::new();
    let mut completed = memo::Memo::default();
    fn push(
        work: &mut Working<'_>,
        todo: &mut Vec<(ExprId, bool)>,
        id: (ExprId, bool),
    ) -> Result<(), Stop> {
        work.budget.reserve_frames(1)?;
        if let Err(error) = scheme::push(work, todo, id) {
            work.budget.release_frames(1)?;
            return Err(error);
        }
        Ok(())
    }
    let result = (|| {
        push(work, &mut todo, (root, false))?;
        while let Some((id, finish)) = todo.pop() {
            work.budget.release_frames(1)?;
            work.budget.charge_work(1)?;
            work.budget.observe(Event::MachineSteps, 1);
            if finish {
                completed.insert(id, 0, work.budget)?;
                continue;
            }
            if completed.contains(id, 0, work.budget)? {
                continue;
            }
            push(work, &mut todo, (id, true))?;
            match raw_kind(work, id)? {
                #[allow(
                    clippy::collapsible_match,
                    reason = "keeps the fallible membership query out of a match guard"
                )]
                ExprKind::Constant(name, _) => {
                    if member(name, work.names, work.budget)? {
                        return Ok(false);
                    }
                }
                ExprKind::App(a, b) | ExprKind::Pi(_, a, b, _) | ExprKind::Lambda(_, a, b, _) => {
                    push(work, &mut todo, (b, false))?;
                    push(work, &mut todo, (a, false))?;
                }
                ExprKind::Let(_, a, b, c, _) => {
                    push(work, &mut todo, (c, false))?;
                    push(work, &mut todo, (b, false))?;
                    push(work, &mut todo, (a, false))?;
                }
                ExprKind::Projection(name, _, a) => {
                    if member(name, work.names, work.budget)? {
                        return Ok(false);
                    };
                    push(work, &mut todo, (a, false))?;
                }
                _ => (),
            }
        }
        Ok(true)
    })();
    let remaining = todo.len();
    let bytes = todo.capacity() * 8;
    drop(todo);
    let frames = work.budget.release_frames(remaining);
    let storage = work.budget.release(bytes as u64);
    frames?;
    storage?;
    completed.retire(work.budget)?;
    result
}
// Syntax-only family identity: the raw pass never consumes serialized flags.
#[derive(Clone, Copy)]
struct RawFamily {
    name: NameId,
    num_params: u32,
}
trait RawFamilies {
    fn raw_family(&self, index: usize) -> Result<RawFamily, ResourceError>;
}
impl RawFamilies for [Inductive] {
    fn raw_family(&self, index: usize) -> Result<RawFamily, ResourceError> {
        let family = self.get(index).ok_or(ResourceError::Invariant)?;
        Ok(RawFamily {
            name: family.name,
            num_params: family.num_params,
        })
    }
}
fn raw_constructor(
    work: &mut Working<'_>,
    family: &Inductive,
    members: &families::FamilySet,
    block: &[Inductive],
    parameters: &[NameId],
    ty: ExprId,
) -> Result<bool, Stop> {
    raw_constructor_template(
        work,
        RawFamily {
            name: family.name,
            num_params: family.num_params,
        },
        members,
        block,
        parameters,
        ty,
    )
}
fn raw_constructor_template<T: RawFamilies + ?Sized>(
    work: &mut Working<'_>,
    family: RawFamily,
    members: &families::FamilySet,
    block: &T,
    parameters: &[NameId],
    ty: ExprId,
) -> Result<bool, Stop> {
    let mut current = ty;
    for _ in 0..family.num_params {
        let ExprKind::Pi(_, domain, body, _) = raw_kind(work, current)? else {
            return Err(Stop::Unsupported);
        };
        if !no_block(work, domain, members)? {
            return Ok(false);
        }
        current = body;
    }
    let mut fields = 0u32;
    while let ExprKind::Pi(_, domain, body, _) = raw_kind(work, current)? {
        let depth = family
            .num_params
            .checked_add(fields)
            .ok_or(ResourceError::Counter)?;
        if !raw_uniform_block(work, block, members, parameters, domain, depth)? {
            return Ok(false);
        }
        fields = fields.checked_add(1).ok_or(ResourceError::Counter)?;
        current = body;
    }
    let depth = family
        .num_params
        .checked_add(fields)
        .ok_or(ResourceError::Counter)?;
    raw_family_template(work, family, members, parameters, current, depth)
}
// Original inner domains may reduce away an occurrence. Check raw maximal
// applications at their true binder depth first; WHNF positivity is separate.
fn raw_uniform_block<T: RawFamilies + ?Sized>(
    work: &mut Working<'_>,
    block: &T,
    members: &families::FamilySet,
    parameters: &[NameId],
    root: ExprId,
    depth: u32,
) -> Result<bool, Stop> {
    let mut todo = Vec::new();
    let mut completed = memo::Memo::default();
    let push =
        |work: &mut Working<'_>, todo: &mut Vec<(ExprId, u32, bool)>, item| -> Result<(), Stop> {
            work.budget.reserve_frames(1)?;
            if let Err(error) = scheme::push(work, todo, item) {
                work.budget.release_frames(1)?;
                return Err(error);
            }
            Ok(())
        };
    let result = (|| {
        push(work, &mut todo, (root, depth, false))?;
        while let Some((root, depth, finish)) = todo.pop() {
            work.budget.release_frames(1)?;
            work.budget.charge_work(1)?;
            if finish {
                completed.insert(root, depth, work.budget)?;
                continue;
            }
            if completed.contains(root, depth, work.budget)? {
                continue;
            }
            push(work, &mut todo, (root, depth, true))?;
            let mut head = root;
            while let ExprKind::App(function, argument) = raw_kind(work, head)? {
                push(work, &mut todo, (argument, depth, false))?;
                head = function;
            }
            match raw_kind(work, head)? {
                ExprKind::Constant(name, _) => {
                    // The approved annotation rule does not erase a raw family
                    // occurrence from a dropped default/tactic argument.
                    if crate::check::environment::annotations::annotation(
                        name,
                        work.names,
                        work.budget,
                    )?
                    .is_some()
                        && !no_block(work, root, members)?
                    {
                        return Err(Stop::Unsupported);
                    }
                    if let Some(member) = members.find(name, work.names, work.budget)?
                        && !raw_family_template(
                            work,
                            block.raw_family(member)?,
                            members,
                            parameters,
                            root,
                            depth,
                        )?
                    {
                        return Ok(false);
                    }
                }
                ExprKind::Pi(_, domain, body, _) | ExprKind::Lambda(_, domain, body, _) => {
                    push(
                        work,
                        &mut todo,
                        (
                            body,
                            depth.checked_add(1).ok_or(ResourceError::Counter)?,
                            false,
                        ),
                    )?;
                    push(work, &mut todo, (domain, depth, false))?;
                }
                ExprKind::Let(_, ty, value, body, _) => {
                    push(
                        work,
                        &mut todo,
                        (
                            body,
                            depth.checked_add(1).ok_or(ResourceError::Counter)?,
                            false,
                        ),
                    )?;
                    push(work, &mut todo, (value, depth, false))?;
                    push(work, &mut todo, (ty, depth, false))?;
                }
                ExprKind::Projection(name, _, source) => {
                    if members.find(name, work.names, work.budget)?.is_some() {
                        return Err(Stop::Unsupported);
                    }
                    push(work, &mut todo, (source, depth, false))?;
                }
                _ => {}
            }
        }
        Ok(true)
    })();
    let frames = todo.len();
    let bytes = todo.capacity() * 12;
    drop(todo);
    work.budget.release_frames(frames)?;
    work.budget.release(bytes as u64)?;
    completed.retire(work.budget)?;
    result
}
// Only terminal raw family spines enter this specialization after the explicit
// family-free Pi telescope. Nested or erased occurrences remain unsupported.
fn raw_family_template(
    work: &mut Working<'_>,
    family: RawFamily,
    members: &families::FamilySet,
    parameters: &[NameId],
    mut current: ExprId,
    depth: u32,
) -> Result<bool, Stop> {
    // The result must have the raw family head: reduction-equivalent wrappers
    // are not constructor result syntax. The occurrence caller already checked
    // that head; only raw_constructor can reach the completed head mismatch.
    let mut args = Vec::new();
    let result = (|| {
        loop {
            match work.expressions.get(current, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )? {
                ExprKind::App(f, a) => {
                    scheme::push(work, &mut args, a)?;
                    current = f;
                }
                ExprKind::Constant(name, us) => {
                    if !same(work.names, name, family.name, work.budget)? {
                        return Ok(false);
                    }
                    if us.len() != parameters.len() {
                        return Ok(false);
                    }
                    work.budget.charge_work(us.len() as u64 + 1)?;
                    for (&level, &name) in us.iter().zip(parameters) {
                        let LevelKind::Param(actual) = work.levels.get(level, work.budget)?.kind()
                        else {
                            return Ok(false);
                        };
                        if !same(work.names, actual, name, work.budget)? {
                            return Ok(false);
                        }
                    }
                    break;
                }
                _ => return Ok(false),
            }
        }
        args.reverse();
        let p = family.num_params as usize;
        // A cross-family occurrence can precede common-parameter validation.
        // Untrusted target counts must never underflow the binder index.
        if args.len() < p || depth < family.num_params {
            return Ok(false);
        }
        for (index, &a) in args[..p].iter().enumerate() {
            if !matches!(raw_kind(work,a)?,ExprKind::Bound(n) if n==depth-1-index as u32) {
                return Ok(false);
            }
        }
        for &a in &args[p..] {
            if !no_block(work, a, members)? {
                return Ok(false);
            }
        }
        Ok(true)
    })();
    let bytes = args.capacity() * 4;
    drop(args);
    work.budget.release(bytes as u64)?;
    result
}
impl State {
    pub(super) fn check_fieldless(
        &mut self,
        request: &Request<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
    ) -> Result<Admission, FailureReport> {
        if request.types.iter().any(|family| family.num_nested != 0) {
            return self.check_original_nested(request, ordinal, decoder, budget);
        }
        if request.types.len() > 1 {
            return self.check_mutual(request, ordinal, decoder, budget);
        }
        let mut rules = Vec::new();
        let result = self.fieldless_inner(request, ordinal, decoder, budget, &mut rules);
        let bytes = rules.capacity() * std::mem::size_of::<NullaryRule>();
        drop(rules);
        if bytes != 0 {
            budget
                .release(bytes as u64)
                .map_err(ResourceError::failure_report)?;
        }
        result
    }
    fn fieldless_inner(
        &mut self,
        request: &Request<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
        rules: &mut Vec<NullaryRule>,
    ) -> Result<Admission, FailureReport> {
        let resource = ResourceError::failure_report;
        budget.charge_work(32).map_err(resource)?;
        let next = self
            .checked
            .checked_add(1)
            .ok_or_else(|| resource(ResourceError::Counter))?;
        if ordinal != next {
            return Err(resource(ResourceError::Invariant));
        }
        let [family] = request.types else {
            return Err(unsupported());
        };
        if family.is_unsafe || request.constructors.iter().any(|c| c.is_unsafe) {
            #[cfg(feature = "introspection")]
            super::capture(
                request,
                decoder,
                budget,
                &[crate::report::failure_snapshot::Rule::DeclarationPolicy],
                &[crate::report::failure_snapshot::Identity::name(
                    crate::report::failure_snapshot::Role::Declaration,
                    family.name,
                )],
                None,
            );
            return Err(unsupported());
        }
        // Nested translation is outside this slice. Serialized metadata may
        // select decline, never authority: zero still requires full derivation.
        // In particular, several valid nested recursors are not extra-rec errors.
        if family.num_nested != 0 {
            return Err(unsupported());
        }
        let parameters = list(request.names, family.parameters).map_err(resource)?;
        let constructors = list(request.names, family.constructors).map_err(resource)?;
        let all = list(request.names, family.all).map_err(resource)?;
        let (names, _, expressions) = decoder.syntax();
        if constructors.len() != request.constructors.len()
            || !singleton(names, all, family.name, budget).map_err(resource)?
        {
            return Ok(Admission::TypeMismatch);
        }
        let [recursor] = request.recursors else {
            return Ok(Admission::TypeMismatch);
        };
        let rec_all = list(request.names, recursor.all).map_err(resource)?;
        let rec_parameters = list(request.names, recursor.parameters).map_err(resource)?;
        if !suffix(names, recursor.name, family.name, "rec", budget).map_err(resource)?
            || !singleton(names, rec_all, family.name, budget).map_err(resource)?
        {
            return Ok(Admission::TypeMismatch);
        }
        for (index, &name) in constructors.iter().enumerate() {
            let mut found = None;
            for c in request.constructors {
                budget.charge_work(1).map_err(resource)?;
                if same(names, name, c.name, budget).map_err(resource)? {
                    if found.is_some() {
                        return Ok(Admission::TypeMismatch);
                    }
                    found = Some(c);
                }
            }
            let Some(c) = found else {
                return Ok(Admission::TypeMismatch);
            };
            for &prior in &constructors[..index] {
                budget.charge_work(1).map_err(resource)?;
                if same(names, prior, name, budget).map_err(resource)? {
                    return Ok(Admission::TypeMismatch);
                }
            }
            if same(names, name, family.name, budget).map_err(resource)?
                || same(names, name, recursor.name, budget).map_err(resource)?
                || !same(names, c.inductive, family.name, budget).map_err(resource)?
                || c.index != index as u32
                || c.num_params != family.num_params
                || !parameters_equal(
                    names,
                    list(request.names, c.parameters).map_err(resource)?,
                    parameters,
                    budget,
                )
                .map_err(resource)?
            {
                return Ok(Admission::TypeMismatch);
            }
        }
        let before = self.environment.len();
        for name in std::iter::once(family.name)
            .chain(constructors.iter().copied())
            .chain(std::iter::once(recursor.name))
        {
            if self
                .environment
                .lookup(name, before, names, budget)
                .map_err(resource)?
                .is_some()
            {
                return Ok(Admission::Duplicate);
            }
        }
        let expression_end = expressions.len();
        let level_end = decoder.syntax().1.len();
        let scope = |formation: Option<Formation>, parameters| Scope {
            parameters,
            before: formation.map_or(before, |p| p.before()),
            mode: Mode::Safe,
            expression_end,
            level_end,
            formation,
        };
        let mut raw = true;
        let mut summary: Option<(usize, LevelPositive, LevelZero)> = None;
        let negative = decoder
            .declaration_session(budget, |work| {
                work.check_input_scope(parameters, &[family.ty])?;
                families::with_set(
                    work,
                    request.types.iter().map(|family| family.name),
                    |work, members| {
                        for constructor in request.constructors {
                            work.check_input_scope(parameters, &[constructor.ty])?;
                            if !raw_constructor(
                                work,
                                family,
                                members,
                                request.types,
                                parameters,
                                constructor.ty,
                            )? {
                                #[cfg(feature = "introspection")]
                                capture_work(
                                    work,
                                    family.name,
                                    &[crate::report::failure_snapshot::Rule::ConstructorValidation],
                                    &[
                                        crate::report::failure_snapshot::Identity::name(
                                            crate::report::failure_snapshot::Role::Declaration,
                                            constructor.name,
                                        ),
                                        crate::report::failure_snapshot::Identity::expression(
                                            crate::report::failure_snapshot::Role::Type,
                                            constructor.ty,
                                        ),
                                    ],
                                );
                                raw = false;
                                return Ok(());
                            }
                        }
                        Ok(())
                    },
                )?;
                if !raw {
                    return Ok(());
                }
                with_scratch(work, |work, s| {
                    // Pre-staging authority: committed environment only;
                    // the staged pass below re-types the same family.
                    work.with_pre_staging_sorts(|work| {
                        s.family(work, request, scope(None, parameters), &self.environment)
                    })?;
                    let level = work
                        .levels
                        .get(s.result.ok_or(ResourceError::Invariant)?, work.budget)?;
                    summary = Some((s.indices, level.positive(), level.zero()));
                    Ok(())
                })
            })
            .map_err(|e| e.failure_report())?;
        if negative.is_some() || !raw {
            return Ok(Admission::TypeMismatch);
        }
        let (indices, positive, zero) =
            summary.ok_or_else(|| resource(ResourceError::Invariant))?;
        let num_indices = u32::try_from(indices).map_err(|_| resource(ResourceError::Counter))?;
        let n = u32::try_from(constructors.len()).map_err(|_| resource(ResourceError::Counter))?;
        if family.num_indices != num_indices
            || recursor.num_params != family.num_params
            || recursor.num_indices != num_indices
            || recursor.num_motives != 1
            || recursor.num_minors != n
            || recursor.rules.start != 0
            || recursor.rules.len != n
            || request.rules.len() != constructors.len()
            || recursor.is_unsafe
        {
            return Ok(Admission::TypeMismatch);
        }
        let mut phase = self
            .environment
            .begin_stage(expression_end, level_end, budget)
            .map_err(resource)?;
        phase = self
            .environment
            .stage_signature(
                phase,
                SignatureInput {
                    kind: SignatureKind::Inductive,
                    name: family.name,
                    parameters,
                    ty: family.ty,
                    all,
                },
                decoder.syntax().0,
                budget,
            )
            .map_err(resource)?;
        let mut valid_constructors = true;
        let mut large_fields = true;
        let mut recursive = false;
        let mut reflexive = false;
        let negative = decoder
            .declaration_session(budget, |work| {
                with_scratch(work, |work, s| {
                    s.family(
                        work,
                        request,
                        scope(Some(phase), parameters),
                        &self.environment,
                    )?;
                    if !s.constructors(
                        work,
                        request,
                        scope(Some(phase), parameters),
                        &self.environment,
                    )? {
                        #[cfg(feature = "introspection")]
                        capture_work(
                            work,
                            family.name,
                            &[
                                crate::report::failure_snapshot::Rule::ConstructorValidation,
                                crate::report::failure_snapshot::Rule::Positivity,
                            ],
                            &[crate::report::failure_snapshot::Identity::expression(
                                crate::report::failure_snapshot::Role::Type,
                                family.ty,
                            )],
                        );
                        valid_constructors = false;
                        return Ok(());
                    }
                    large_fields = s.large_fields;
                    recursive = s.recursive;
                    reflexive = s.reflexive;
                    for (i, &name) in constructors.iter().enumerate() {
                        let fields = s.field_count(i)?;
                        let mut declaration = None;
                        for c in request.constructors {
                            work.budget.charge_work(1)?;
                            if same(work.names, name, c.name, work.budget)? {
                                declaration = Some(c);
                                break;
                            }
                        }
                        let declaration = declaration.ok_or(ResourceError::Invariant)?;
                        let rule = &request.rules[i];
                        if declaration.num_fields != fields
                            || rule.num_fields != fields
                            || !same(work.names, rule.constructor, name, work.budget)?
                        {
                            valid_constructors = false;
                            return Ok(());
                        }
                        scheme::push(
                            work,
                            rules,
                            NullaryRule {
                                constructor: name,
                                rhs: rule.rhs,
                                num_fields: fields,
                            },
                        )?;
                    }
                    Ok(())
                })
            })
            .map_err(|e| e.failure_report())?;
        if negative.is_some()
            || !valid_constructors
            || family.is_recursive != recursive
            || family.is_reflexive != reflexive
        {
            return Ok(Admission::TypeMismatch);
        }
        // Direction of use: Proven permits the large
        // recursor shape; NotProven contributes nothing and falls back to the
        // structural large_fields derivation. `zero` is the total decision.
        let large = positive == LevelPositive::Proven || (constructors.len() <= 1 && large_fields);
        let k = zero == LevelZero::Zero && constructors.len() == 1 && rules[0].num_fields == 0;
        if recursor.k != k {
            return Ok(Admission::TypeMismatch);
        }
        let names = decoder.syntax().0;
        let universe = if large {
            if rec_parameters.len() != parameters.len() + 1
                || !parameters_equal(names, &rec_parameters[1..], parameters, budget)
                    .map_err(resource)?
                || !fresh_parameter(names, parameters, rec_parameters[0], budget)
                    .map_err(resource)?
            {
                return Ok(Admission::TypeMismatch);
            }
            Some(rec_parameters[0])
        } else {
            if !parameters_equal(names, rec_parameters, parameters, budget).map_err(resource)? {
                return Ok(Admission::TypeMismatch);
            }
            None
        };
        for &name in constructors {
            let mut ty = None;
            for c in request.constructors {
                budget.charge_work(1).map_err(resource)?;
                if same(decoder.syntax().0, name, c.name, budget).map_err(resource)? {
                    ty = Some(c.ty);
                    break;
                }
            }
            phase = self
                .environment
                .stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Constructor,
                        name,
                        parameters,
                        ty: ty.ok_or_else(|| resource(ResourceError::Invariant))?,
                        all,
                    },
                    decoder.syntax().0,
                    budget,
                )
                .map_err(resource)?;
        }
        let mut matched = true;
        let negative = decoder
            .declaration_session(budget, |work| {
                with_scratch(work, |work, s| {
                    let scope = scope(Some(phase), rec_parameters);
                    s.family(work, request, scope, &self.environment)?;
                    if !s.constructors(work, request, scope, &self.environment)? {
                        return Err(ResourceError::Invariant.into());
                    }
                    s.add_motives(work, universe, scope, &self.environment)?;
                    let generated = s.recursor(work, family.name)?;
                    work.check_root_scope(rec_parameters, &[generated])?;
                    work.check_type(
                        generated,
                        false,
                        ReductionPath::start(),
                        scope,
                        &self.environment,
                    )?;
                    matched = scheme::matches(work, generated, recursor.ty)?;
                    if !matched {
                        #[cfg(feature = "introspection")]
                        capture_work(
                            work,
                            family.name,
                            &[crate::report::failure_snapshot::Rule::ExportMatch],
                            &[
                                crate::report::failure_snapshot::Identity::expression(
                                    crate::report::failure_snapshot::Role::Expected,
                                    generated,
                                ),
                                crate::report::failure_snapshot::Identity::expression(
                                    crate::report::failure_snapshot::Role::Actual,
                                    recursor.ty,
                                ),
                            ],
                        );
                    }
                    Ok(())
                })
            })
            .map_err(|e| e.failure_report())?;
        if negative.is_some() {
            return Err(resource(ResourceError::Invariant));
        }
        if !matched {
            return Ok(Admission::TypeMismatch);
        }
        phase = self
            .environment
            .stage_signature(
                phase,
                SignatureInput {
                    kind: SignatureKind::Recursor,
                    name: recursor.name,
                    parameters: rec_parameters,
                    ty: recursor.ty,
                    all: rec_all,
                },
                decoder.syntax().0,
                budget,
            )
            .map_err(resource)?;
        if !rules.is_empty() {
            let negative = decoder
                .declaration_session(budget, |work| {
                    with_scratch(work, |work, s| {
                        let scope = scope(Some(phase), rec_parameters);
                        s.family(work, request, scope, &self.environment)?;
                        if !s.constructors(work, request, scope, &self.environment)? {
                            return Err(ResourceError::Invariant.into());
                        }
                        s.add_motives(work, universe, scope, &self.environment)?;
                        for (i, rule) in rules.iter().enumerate() {
                            let rhs = s.rhs(work, recursor.name, i)?;
                            work.check_root_scope(rec_parameters, &[rhs])?;
                            s.recheck(work, rhs, i, scope, &self.environment)?;
                            if !scheme::matches(work, rhs, rule.rhs)? {
                                #[cfg(feature = "introspection")]
                                capture_work(
                                    work,
                                    family.name,
                                    &[crate::report::failure_snapshot::Rule::ExportMatch],
                                    &[
                                        crate::report::failure_snapshot::Identity::expression(
                                            crate::report::failure_snapshot::Role::Expected,
                                            rhs,
                                        ),
                                        crate::report::failure_snapshot::Identity::expression(
                                            crate::report::failure_snapshot::Role::Actual,
                                            rule.rhs,
                                        ),
                                    ],
                                );
                                matched = false;
                                break;
                            }
                        }
                        Ok(())
                    })
                })
                .map_err(|e| e.failure_report())?;
            if negative.is_some() {
                return Err(resource(ResourceError::Invariant));
            }
            if !matched {
                return Ok(Admission::TypeMismatch);
            }
        }
        let predicates = self
            .environment
            .prepare_predicate_group(
                request,
                decoder.syntax().0,
                decoder.syntax().1,
                decoder.syntax().2,
                budget,
            )
            .map_err(resource)?;
        let string = self
            .environment
            .prepare_string_group(
                self.environment.string,
                request,
                decoder.syntax().0,
                decoder.syntax().1,
                decoder.syntax().2,
                budget,
            )
            .map_err(resource)?;
        let native_natural = self
            .environment
            .prepare_native_natural_group(
                self.environment.native_natural,
                &string,
                request,
                decoder.syntax().0,
                decoder.syntax().1,
                decoder.syntax().2,
                budget,
            )
            .map_err(resource)?;
        let finite = self
            .environment
            .prepare_finite_group(
                self.environment.finite,
                request,
                decoder.syntax().0,
                decoder.syntax().1,
                decoder.syntax().2,
                budget,
            )
            .map_err(resource)?;
        let natural = self
            .environment
            .prepare_natural(
                request,
                decoder.syntax().0,
                decoder.syntax().1,
                decoder.syntax().2,
                budget,
            )
            .map_err(resource)?;
        let token = self
            .environment
            .prepare_nullary_commit(
                phase,
                NullaryMetadata {
                    nonrecursive: !recursive,
                    family: family.name,
                    recursor: recursor.name,
                    num_params: family.num_params,
                    num_indices,
                    k,
                    rules,
                },
                decoder.syntax().0,
                budget,
            )
            .map_err(resource)?;
        let temporary = std::mem::take(rules);
        let bytes = temporary.capacity() * std::mem::size_of::<NullaryRule>();
        drop(temporary);
        budget.release(bytes as u64).map_err(resource)?;
        token.with_natural(natural).commit();
        self.environment.commit_predicates(predicates);
        self.environment.native_natural = native_natural;
        self.environment.string = string;
        self.environment.finite = finite;
        self.checked = next;
        budget.checked_declarations(next);
        budget.observe(Event::DeclarationsInstalled, u64::from(n) + 2);
        Ok(Admission::Installed)
    }
}
