//! Terminal-only specialization queue. No entry is an installed or checked helper.
//! Original templates come only from the frozen committed prefix; all generated
//! roots and saved keys belong to the enclosing declaration session.
use super::*;
use crate::check::environment::{Safety, StoredKind, TypeSource};
use crate::syntax::levels::{Instance, LevelId};
use std::hash::{Hash, Hasher};
mod expanded;
mod key;
mod matching;
mod naming;
mod parameters;
mod publication;
mod recursors;
mod restore;
mod restored;
mod rewrite;
mod validation;

#[derive(Clone, Copy)]
struct Family {
    prior: NameId,
    helper: NameId,
    ty: ExprId,
    key: u32,
    constructors: u32,
    count: u32,
}
#[derive(Clone, Copy)]
struct Constructor {
    prior: NameId,
    helper: NameId,
    ty: ExprId,
}
#[derive(Clone, Copy)]
struct Key {
    root: ExprId,
    start: u32,
    len: u32,
    hash: u64,
}
const _: () = assert!(size_of::<Family>() == 24);
const _: () = assert!(size_of::<Constructor>() == 12);
const _: () = assert!(size_of::<Key>() == 24);

#[derive(Default)]
pub(super) struct Queue {
    families: Vec<Family>,
    constructors: Vec<Constructor>,
    keys: Vec<Key>,
    bytes: Vec<u8>,
    next_name: u32,
    original_constructors: Vec<ExprId>,
}
const _: () = assert!(size_of::<Queue>() == 128);
fn push<T>(v: &mut Vec<T>, x: T, b: &mut Budget) -> Result<(), Stop> {
    let n = v.len().checked_add(1).ok_or(ResourceError::Counter)?;
    b.grow_vec(v, n)?;
    v.push(x);
    Ok(())
}
fn release<T>(v: Vec<T>, b: &mut Budget) -> Result<(), ResourceError> {
    let bytes = v
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)?;
    drop(v);
    b.release(bytes as u64)
}
fn push_frame<T>(v: &mut Vec<T>, x: T, b: &mut Budget) -> Result<(), Stop> {
    b.reserve_frames(1)?;
    if let Err(error) = push(v, x, b) {
        b.release_frames(1)?;
        return Err(error);
    }
    Ok(())
}
fn pop_frame<T>(v: &mut Vec<T>, b: &mut Budget) -> Result<Option<T>, Stop> {
    let item = v.pop();
    if item.is_some() {
        b.release_frames(1)?;
    }
    Ok(item)
}
fn release_stack<T>(v: Vec<T>, b: &mut Budget) -> Result<(), ResourceError> {
    let frames = b.release_frames(v.len());
    let storage = release(v, b);
    frames?;
    storage
}
impl Queue {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn run(
        &mut self,
        request: &Request<'_>,
        order: &Order,
        work: &mut Working<'_>,
        environment: &Environment,
        before: usize,
        phase: Formation,
        ends: (usize, usize),
    ) -> Result<(), Stop> {
        let first = request
            .types
            .get(*order.families.first().ok_or(ResourceError::Invariant)? as usize)
            .ok_or(ResourceError::Invariant)?;
        if request
            .types
            .iter()
            .any(|f| f.num_params != first.num_params)
        {
            return Err(Stop::Unsupported);
        }
        let mut parameters = parameters::Parameters::default();
        let scope = Scope {
            parameters: list(request.names, first.parameters)?,
            before: phase.before(),
            mode: Mode::Safe,
            expression_end: ends.0,
            level_end: ends.1,
            formation: Some(phase),
        };
        let result = (|| {
            // Audited checked-root precondition: original_nested_in_session
            // checked every original family type against the committed prefix
            // and every constructor type under this exact signature-only phase.
            // Ordered syntactic opening transports those checked prefix domains;
            // helpers receive only that prefix evidence, never checked bodies.
            parameters.prepare(first.ty, first.num_params, work)?;
            // This bounded slice declines reserved user syntax before generating names.
            // A current staged name is not covered by fresh()'s committed lookup.
            for name in request
                .types
                .iter()
                .map(|f| f.name)
                .chain(request.constructors.iter().map(|c| c.name))
                .chain(request.recursors.iter().map(|r| r.name))
            {
                naming::public_name(name, work)?;
            }
            for root in request
                .types
                .iter()
                .map(|f| f.ty)
                .chain(request.constructors.iter().map(|c| c.ty))
            {
                check_public_root(root, work)?;
            }
            self.next_name = 1;
            for &index in &order.constructors {
                let ctor = &request.constructors[index as usize];
                parameters.with_open(ctor.ty, work, scope, environment, |root, work| {
                    self.visit(root, request, &parameters, work, environment, before, ends)
                })?;
            }
            let mut cursor = 0;
            while cursor < self.families.len() {
                let f = self.families[cursor];
                // Retained roots must remain closed templates at this first boundary;
                // later phases may not mistake an escaped local for a block parameter.
                if work.expressions.get(f.ty, work.budget)?.loose_range() != 0
                    || self.keys.get(f.key as usize).is_none()
                {
                    return Err(ResourceError::Invariant.into());
                }
                // The whole prior mutual block was registered before these visits.
                for c in f.constructors
                    ..f.constructors
                        .checked_add(f.count)
                        .ok_or(ResourceError::Counter)?
                {
                    let constructor = self.constructors[c as usize];
                    if same(
                        work.names,
                        constructor.prior,
                        constructor.helper,
                        work.budget,
                    )? {
                        return Err(ResourceError::Invariant.into());
                    }
                    let root = constructor.ty;
                    parameters.with_open(root, work, scope, environment, |root, work| {
                        self.visit(root, request, &parameters, work, environment, before, ends)
                    })?;
                }
                cursor += 1;
            }
            self.rewrite_constructors(request, order, &parameters, work, environment, before)?;
            // Discovery/rewrite bytes are never reused after this boundary.
            // Close saved representatives before their canonical locals retire;
            // subsequent restoration consumes these lambda recipes as syntax.
            if first.num_params != 0 {
                for key in &mut self.keys {
                    key.root = parameters.recipe(key.root, work)?;
                    let closed = work.expressions.get(key.root, work.budget)?;
                    if closed.has_free() || closed.loose_range() != 0 {
                        return Err(ResourceError::Invariant.into());
                    }
                }
            }
            Ok(())
        })();
        finish_parameters(result, parameters, work).map_err(|error| match error {
            Stop::Judgment(_) => Stop::Unsupported,
            Stop::Inference(error) => Stop::Observation(error),
            other => other,
        })
    }
    #[allow(clippy::too_many_arguments)]
    fn visit(
        &mut self,
        root: ExprId,
        request: &Request<'_>,
        parameters: &parameters::Parameters,
        work: &mut Working<'_>,
        env: &Environment,
        before: usize,
        ends: (usize, usize),
    ) -> Result<(), Stop> {
        let mut stack = Vec::new();
        let result = (|| {
            push_frame(&mut stack, root, work.budget)?;
            while let Some(root) = pop_frame(&mut stack, work.budget)? {
                work.budget.charge_work(1)?;
                if self.register(root, request, parameters, work, env, before, ends)? {
                    // Discovery follows the replacement boundary: the complete
                    // application would be replaced once, without revisiting its
                    // arguments or indices. Original typing/namespace checks above
                    // still cover them. Later rewriting must preserve index roots
                    // unchanged, then expanded validation checks the new template.
                    continue;
                }
                for child in children(root, work)?.into_iter().rev().flatten() {
                    push_frame(&mut stack, child, work.budget)?;
                }
            }
            Ok(())
        })();
        release_stack(stack, work.budget)?;
        result
    }
    fn occurs(
        &self,
        root: ExprId,
        request: &Request<'_>,
        work: &mut Working<'_>,
    ) -> Result<bool, Stop> {
        let mut stack = Vec::new();
        let result = (|| {
            push_frame(&mut stack, root, work.budget)?;
            while let Some(root) = pop_frame(&mut stack, work.budget)? {
                work.budget.charge_work(1)?;
                if let ExprKind::Constant(name, _) = work.expressions.get(root, work.budget)?.kind(
                    work.expressions,
                    work.levels,
                    work.budget,
                )? {
                    for family in request.types {
                        if same(work.names, name, family.name, work.budget)? {
                            return Ok(true);
                        }
                    }
                    for family in &self.families {
                        if same(work.names, name, family.helper, work.budget)? {
                            return Ok(true);
                        }
                    }
                }
                for child in children(root, work)?.into_iter().flatten() {
                    push_frame(&mut stack, child, work.budget)?;
                }
            }
            Ok(false)
        })();
        release_stack(stack, work.budget)?;
        result
    }
    #[allow(clippy::too_many_arguments)]
    fn register(
        &mut self,
        root: ExprId,
        request: &Request<'_>,
        parameters: &parameters::Parameters,
        work: &mut Working<'_>,
        env: &Environment,
        before: usize,
        ends: (usize, usize),
    ) -> Result<bool, Stop> {
        if !matches!(
            work.expressions.get(root, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget
            )?,
            ExprKind::App(..)
        ) {
            return Ok(false);
        }
        let mut args = Vec::new();
        let mut universes = Vec::new();
        let mut members = Vec::new();
        let result = (|| {
            let mut head = root;
            while let ExprKind::App(f, a) = work.expressions.get(head, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )? {
                push(&mut args, a, work.budget)?;
                head = f;
            }
            let ExprKind::Constant(name, levels) = work.expressions.get(head, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )?
            else {
                return Ok(false);
            };
            let Some(metadata) = env.inductive(name, before, work.names, work.budget)? else {
                return Ok(false);
            };
            let count = metadata.num_params as usize;
            if count == 0 || args.len() < count {
                return Ok(false);
            }
            work.budget.grow_vec(&mut universes, levels.len())?;
            universes.extend_from_slice(levels);
            args.reverse();
            let mut occurs = false;
            let mut loose = false;
            for &arg in &args[..count] {
                loose |= work.expressions.get(arg, work.budget)?.loose_range() != 0;
                occurs |= self.occurs(arg, request, work)?;
            }
            if !occurs {
                return Ok(false);
            }
            if loose {
                return Err(Stop::Unsupported);
            }
            let partial = application(name, &universes, &args[..count], work)?;
            if self.find(partial, work)?.is_some() {
                return Ok(true);
            }
            let signature = env
                .lookup(name, before, work.names, work.budget)?
                .ok_or(ResourceError::Invariant)?;
            if signature.safety != Safety::Safe {
                return Err(Stop::Unsupported);
            }
            work.budget.grow_vec(&mut members, signature.all.len())?;
            members.extend_from_slice(signature.all);
            // Register every member and key before cloning any constructors.
            let start = self.families.len();
            for &member in &members {
                let metadata = env
                    .inductive(member, before, work.names, work.budget)?
                    .ok_or(ResourceError::Invariant)?;
                if metadata.num_params as usize != count {
                    return Err(ResourceError::Invariant.into());
                }
                let partial = application(member, &universes, &args[..count], work)?;
                if self.find(partial, work)?.is_some() {
                    return Err(ResourceError::Invariant.into());
                }
                let key = self.save(partial, work)?;
                let helper = naming::fresh(member, &mut self.next_name, env, before, work)?;
                let ty = specialize(member, &universes, &args[..count], env, before, ends, work)?;
                let ty = parameters.close(ty, work)?;
                push(
                    &mut self.families,
                    Family {
                        prior: member,
                        helper,
                        ty,
                        key,
                        constructors: 0,
                        count: 0,
                    },
                    work.budget,
                )?;
            }
            for i in start..self.families.len() {
                let family = self.families[i];
                let metadata = env
                    .inductive(family.prior, before, work.names, work.budget)?
                    .ok_or(ResourceError::Invariant)?;
                let offset =
                    u32::try_from(self.constructors.len()).map_err(|_| ResourceError::Counter)?;
                for (index, rule) in metadata.constructors.iter().enumerate() {
                    let ctor = env
                        .constructor(rule.constructor, before, work.names, work.budget)?
                        .ok_or(ResourceError::Invariant)?;
                    if ctor.index as usize != index
                        || !same(work.names, ctor.family, family.prior, work.budget)?
                    {
                        return Err(ResourceError::Invariant.into());
                    }
                    let helper = naming::constructor(ctor.name, family.prior, family.helper, work)?;
                    let ty = specialize(
                        ctor.name,
                        &universes,
                        &args[..count],
                        env,
                        before,
                        ends,
                        work,
                    )?;
                    let ty = parameters.close(ty, work)?;
                    push(
                        &mut self.constructors,
                        Constructor {
                            prior: ctor.name,
                            helper,
                            ty,
                        },
                        work.budget,
                    )?;
                }
                self.families[i].constructors = offset;
                self.families[i].count = u32::try_from(metadata.constructors.len())
                    .map_err(|_| ResourceError::Counter)?;
            }
            Ok(true)
        })();
        let a = release(args, work.budget);
        let z = release(universes, work.budget);
        let m = release(members, work.budget);
        a?;
        z?;
        m?;
        result
    }
    fn find(&self, root: ExprId, work: &mut Working<'_>) -> Result<Option<usize>, Stop> {
        for (i, key) in self.keys.iter().enumerate() {
            work.budget.charge_work(1)?;
            if key.root == root {
                return Ok(Some(i));
            }
        }
        let mut bytes = Vec::new();
        let result = (|| {
            key::encode(root, &mut bytes, work)?;
            let mut h = crate::syntax::hash::FastHasher::new();
            bytes.hash(&mut h);
            let hash = h.finish();
            for (i, k) in self.keys.iter().enumerate() {
                work.budget.charge_work(1)?;
                if k.hash == hash && k.len as usize == bytes.len() {
                    work.budget.charge_work(bytes.len() as u64)?;
                    if self
                        .bytes
                        .get(
                            k.start as usize
                                ..k.start.checked_add(k.len).ok_or(ResourceError::Counter)?
                                    as usize,
                        )
                        .ok_or(ResourceError::Invariant)?
                        == bytes
                    {
                        return Ok(Some(i));
                    }
                }
            }
            Ok(None)
        })();
        release(bytes, work.budget)?;
        result
    }
    fn save(&mut self, root: ExprId, work: &mut Working<'_>) -> Result<u32, Stop> {
        let start = self.bytes.len();
        key::encode(root, &mut self.bytes, work)?;
        let mut h = crate::syntax::hash::FastHasher::new();
        self.bytes[start..].hash(&mut h);
        let index = u32::try_from(self.keys.len()).map_err(|_| ResourceError::Counter)?;
        push(
            &mut self.keys,
            Key {
                root,
                start: u32::try_from(start).map_err(|_| ResourceError::Counter)?,
                len: u32::try_from(self.bytes.len() - start).map_err(|_| ResourceError::Counter)?,
                hash: h.finish(),
            },
            work.budget,
        )?;
        Ok(index)
    }
    pub(super) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let a = release(self.families, b);
        let z = release(self.constructors, b);
        let k = release(self.keys, b);
        let v = release(self.bytes, b);
        let r = release(self.original_constructors, b);
        a?;
        z?;
        k?;
        v?;
        r
    }
}
fn check_public_root(root: ExprId, work: &mut Working<'_>) -> Result<(), Stop> {
    let mut stack = Vec::new();
    let result = (|| {
        push_frame(&mut stack, root, work.budget)?;
        while let Some(root) = pop_frame(&mut stack, work.budget)? {
            match work.expressions.get(root, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )? {
                ExprKind::Constant(name, _) | ExprKind::Projection(name, _, _) => {
                    naming::public_name(name, work)?
                }
                _ => (),
            }
            for child in children(root, work)?.into_iter().flatten() {
                push_frame(&mut stack, child, work.budget)?;
            }
        }
        Ok(())
    })();
    release_stack(stack, work.budget)?;
    result
}
fn application(
    name: NameId,
    levels: &[LevelId],
    args: &[ExprId],
    work: &mut Working<'_>,
) -> Result<ExprId, Stop> {
    let mut root = work.expressions.append(
        ExprKind::Constant(name, levels),
        work.levels,
        work.names,
        work.budget,
    )?;
    for &arg in args {
        root = work.expressions.append(
            ExprKind::App(root, arg),
            work.levels,
            work.names,
            work.budget,
        )?;
    }
    Ok(root)
}
#[allow(clippy::too_many_arguments)]
fn specialize(
    name: NameId,
    universes: &[LevelId],
    arguments: &[ExprId],
    env: &Environment,
    before: usize,
    ends: (usize, usize),
    work: &mut Working<'_>,
) -> Result<ExprId, Stop> {
    let sig = env
        .lookup(name, before, work.names, work.budget)?
        .ok_or(ResourceError::Invariant)?;
    if sig.safety != Safety::Safe || !matches!(sig.kind, StoredKind::Signature(_)) {
        return Err(Stop::Unsupported);
    }
    let TypeSource::Original(ty) = sig.ty else {
        return Err(ResourceError::Invariant.into());
    };
    let mut ty = work.expressions.with_uncached_universe_substitution(
        work.levels,
        work.names,
        Instance {
            expression_end: ends.0,
            level_end: ends.1,
            parameters: sig.parameters,
            replacements: universes,
        },
        work.budget,
        |s| s.apply(ty),
    )?;
    for _ in arguments {
        let ExprKind::Pi(_, _, body, _) = work.expressions.get(ty, work.budget)?.kind(
            work.expressions,
            work.levels,
            work.budget,
        )?
        else {
            return Err(ResourceError::Invariant.into());
        };
        ty = body;
    }
    let mut reverse = Vec::new();
    let result = (|| {
        work.budget.grow_vec(&mut reverse, arguments.len())?;
        reverse.extend(arguments.iter().rev().copied());
        work.expressions
            .bind_template(ty, &reverse, work.levels, work.names, work.budget)
            .map_err(Stop::from)
    })();
    release(reverse, work.budget)?;
    result
}
fn children(root: ExprId, work: &mut Working<'_>) -> Result<[Option<ExprId>; 3], Stop> {
    Ok(
        match work.expressions.get(root, work.budget)?.kind(
            work.expressions,
            work.levels,
            work.budget,
        )? {
            ExprKind::App(a, b) | ExprKind::Pi(_, a, b, _) | ExprKind::Lambda(_, a, b, _) => {
                [Some(a), Some(b), None]
            }
            ExprKind::Let(_, a, b, c, _) => [Some(a), Some(b), Some(c)],
            ExprKind::Projection(_, _, a) => [Some(a), None, None],
            _ => [None; 3],
        },
    )
}

// Failed retirement is terminal. Preserve every primary cause separately from
// cleanup so an exhausted leave cannot turn an internal failure into a decline.
fn finish_parameters(
    result: Result<(), Stop>,
    parameters: parameters::Parameters,
    work: &mut Working<'_>,
) -> Result<(), Stop> {
    if let Err(error) = parameters.retire(work) {
        work.record_nested_retirement(Err(error));
        return result.and(Err(error.into()));
    }
    result
}
