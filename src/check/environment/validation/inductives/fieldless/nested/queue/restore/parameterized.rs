//! One-pass restoration of saturated common parameter prefixes. Pending recipe
//! identity lives only on the temporary function-spine result stack; it is not a
//! checkedness certificate, cache or property of an expression node.
use super::*;
use crate::syntax::expressions::binding::Binding;

enum Frame {
    Visit(ExprId, u32),
    Finish(ExprId, u32),
}
struct Value {
    root: ExprId,
    pending: Option<u32>,
    consumed: u32,
}
const _: () = assert!(size_of::<Frame>() == 12);
const _: () = assert!(size_of::<Value>() == 16);

impl Restorer<'_> {
    pub(super) fn parameterized_root(
        &self,
        root: ExprId,
        work: &mut Working<'_>,
    ) -> Result<ExprId, Stop> {
        // Only generated outer Pi/lambda parameter telescopes license dropping
        // application arguments. No WHNF or inferred binder substitutes for one.
        let mut prefix = root;
        for _ in 0..self.term_parameters {
            match raw_kind(prefix, work)? {
                ExprKind::Pi(_, _, body, _) | ExprKind::Lambda(_, _, body, _) => prefix = body,
                _ => return Err(Stop::Unsupported),
            }
        }
        let mut stack = Vec::new();
        let mut values = Vec::new();
        let result = (|| {
            push_frame(&mut stack, Frame::Visit(root, 0), work.budget)?;
            while let Some(frame) = pop_frame(&mut stack, work.budget)? {
                work.budget.charge_work(1)?;
                match frame {
                    Frame::Visit(root, depth) => {
                        let children = children(root, work)?;
                        if children[0].is_none() {
                            let value = self.leaf(root, work)?;
                            push_frame(&mut values, value, work.budget)?;
                        } else {
                            let binder = matches!(
                                raw_kind(root, work)?,
                                ExprKind::Pi(..) | ExprKind::Lambda(..) | ExprKind::Let(..)
                            );
                            push_frame(&mut stack, Frame::Finish(root, depth), work.budget)?;
                            for (index, child) in children.into_iter().enumerate().rev() {
                                if let Some(child) = child {
                                    let depth = if binder
                                        && index == if children[2].is_some() { 2 } else { 1 }
                                    {
                                        depth.checked_add(1).ok_or(ResourceError::Counter)?
                                    } else {
                                        depth
                                    };
                                    push_frame(
                                        &mut stack,
                                        Frame::Visit(child, depth),
                                        work.budget,
                                    )?;
                                }
                            }
                        }
                    }
                    Frame::Finish(root, depth) => {
                        let mut changed = children(root, work)?;
                        let mut pending = [None; 3];
                        for index in (0..3).rev() {
                            if changed[index].is_some() {
                                let value = pop_frame(&mut values, work.budget)?
                                    .ok_or(ResourceError::Invariant)?;
                                changed[index] = Some(value.root);
                                if let Some(recipe) = value.pending {
                                    pending[index] = Some((recipe, value.consumed));
                                }
                            }
                        }
                        let application = matches!(raw_kind(root, work)?, ExprKind::App(..));
                        // Pending recipes may propagate along the function edge
                        // only. A short prefix elsewhere supplies no restoration.
                        if pending[1].is_some()
                            || pending[2].is_some()
                            || (!application && pending[0].is_some())
                        {
                            return Err(Stop::Unsupported);
                        }
                        let root = rewrite::rebuild(root, changed, work)?;
                        let value = if let Some((recipe, consumed)) = pending[0] {
                            if depth < self.term_parameters {
                                return Err(Stop::Unsupported);
                            }
                            let expected = depth
                                .checked_sub(1)
                                .and_then(|n| n.checked_sub(consumed))
                                .ok_or(ResourceError::Counter)?;
                            if !matches!(raw_kind(changed[1].ok_or(ResourceError::Invariant)?, work)?, ExprKind::Bound(index) if index == expected)
                            {
                                return Err(Stop::Unsupported);
                            }
                            let consumed = consumed.checked_add(1).ok_or(ResourceError::Counter)?;
                            if consumed == self.term_parameters {
                                Value {
                                    root: self.instantiate(recipe as usize, depth, work)?,
                                    pending: None,
                                    consumed: 0,
                                }
                            } else {
                                Value {
                                    root,
                                    pending: Some(recipe),
                                    consumed,
                                }
                            }
                        } else {
                            Value {
                                root: self.projection(root, work)?,
                                pending: None,
                                consumed: 0,
                            }
                        };
                        push_frame(&mut values, value, work.budget)?;
                    }
                }
            }
            let value = pop_frame(&mut values, work.budget)?.ok_or(ResourceError::Invariant)?;
            if value.pending.is_some() {
                return Err(Stop::Unsupported);
            }
            if !values.is_empty() {
                return Err(ResourceError::Invariant.into());
            }
            Ok(value.root)
        })();
        // Both buffers retire on every route, preserving the operation cause.
        let a = release_stack(stack, work.budget);
        let b = release_stack(values, work.budget);
        for cleanup in [a, b] {
            if let Err(error) = cleanup {
                work.record_nested_retirement(Err(error));
                return result.and(Err(error.into()));
            }
        }
        result
    }

    fn leaf(&self, root: ExprId, work: &mut Working<'_>) -> Result<Value, Stop> {
        let plain = |root| Value {
            root,
            pending: None,
            consumed: 0,
        };
        let (name, count) = match raw_kind(root, work)? {
            ExprKind::Constant(name, levels) => (name, levels.len()),
            ExprKind::Free(_) => return Err(ResourceError::Invariant.into()),
            _ => return Ok(plain(root)),
        };
        let Some(index) = self.find(name, work)? else {
            naming::public_name(name, work)?;
            return Ok(plain(root));
        };
        let end = self
            .queue
            .families
            .len()
            .checked_add(self.queue.constructors.len())
            .ok_or(ResourceError::Counter)?;
        if index >= end {
            return Ok(plain(
                self.constant(root, work)?.ok_or(ResourceError::Invariant)?,
            ));
        }
        if count != self.parameters.len() {
            return Err(Stop::Unsupported);
        }
        let ExprKind::Constant(_, levels) = work.expressions.get(root, work.budget)?.kind(
            work.expressions,
            work.levels,
            work.budget,
        )?
        else {
            return Err(ResourceError::Invariant.into());
        };
        for (&level, &parameter) in levels.iter().zip(self.parameters) {
            let LevelKind::Param(name) = work.levels.get(level, work.budget)?.kind() else {
                return Err(Stop::Unsupported);
            };
            if !same(work.names, name, parameter, work.budget)? {
                return Err(Stop::Unsupported);
            }
        }
        Ok(Value {
            root,
            pending: Some(u32::try_from(index).map_err(|_| ResourceError::Counter)?),
            consumed: 0,
        })
    }

    fn instantiate(
        &self,
        index: usize,
        depth: u32,
        work: &mut Working<'_>,
    ) -> Result<ExprId, Stop> {
        let mut recipe = if index < self.queue.families.len() {
            let family = self.queue.families[index];
            self.queue
                .keys
                .get(family.key as usize)
                .ok_or(ResourceError::Invariant)?
                .root
        } else {
            self.constructor_recipe(index - self.queue.families.len(), work)?
        };
        // Every supplied argument was proved syntactically to be exactly its
        // common outer binder. Strip the closed lambda telescope and lift its
        // body across intervening binders once; this is simultaneous identity
        // substitution, not general beta normalization of exported syntax.
        for _ in 0..self.term_parameters {
            let ExprKind::Lambda(_, _, body, _) = raw_kind(recipe, work)? else {
                return Err(ResourceError::Invariant.into());
            };
            recipe = body;
        }
        let lift = depth
            .checked_sub(self.term_parameters)
            .ok_or(ResourceError::Invariant)?;
        Ok(work.expressions.bind(
            recipe,
            0,
            Binding::Lift(lift),
            work.levels,
            work.names,
            work.budget,
        )?)
    }

    fn constructor_recipe(&self, index: usize, work: &mut Working<'_>) -> Result<ExprId, Stop> {
        let constructor = self
            .queue
            .constructors
            .get(index)
            .ok_or(ResourceError::Invariant)?;
        let mut owner = None;
        for family in &self.queue.families {
            work.budget.charge_work(1)?;
            let start = family.constructors as usize;
            let end = start
                .checked_add(family.count as usize)
                .ok_or(ResourceError::Counter)?;
            if (start..end).contains(&index) && owner.replace(*family).is_some() {
                return Err(ResourceError::Invariant.into());
            }
        }
        let family = owner.ok_or(ResourceError::Invariant)?;
        let mut root = self
            .queue
            .keys
            .get(family.key as usize)
            .ok_or(ResourceError::Invariant)?
            .root;
        let mut prefix = Vec::new();
        let mut args = Vec::new();
        let mut levels = Vec::new();
        let result = (|| {
            for _ in 0..self.term_parameters {
                let ExprKind::Lambda(name, domain, body, annotation) = raw_kind(root, work)? else {
                    return Err(ResourceError::Invariant.into());
                };
                push(&mut prefix, (name, domain, annotation), work.budget)?;
                root = body;
            }
            loop {
                match work.expressions.get(root, work.budget)?.kind(
                    work.expressions,
                    work.levels,
                    work.budget,
                )? {
                    ExprKind::App(f, a) => {
                        push(&mut args, a, work.budget)?;
                        root = f;
                    }
                    ExprKind::Constant(name, original) => {
                        if !same(work.names, name, family.prior, work.budget)? {
                            return Err(ResourceError::Invariant.into());
                        }
                        work.budget.grow_vec(&mut levels, original.len())?;
                        work.budget.charge_work(original.len() as u64)?;
                        levels.extend_from_slice(original);
                        break;
                    }
                    _ => return Err(ResourceError::Invariant.into()),
                }
            }
            args.reverse();
            let mut root = application(constructor.prior, &levels, &args, work)?;
            for &(name, domain, annotation) in prefix.iter().rev() {
                root = work.expressions.append(
                    ExprKind::Lambda(name, domain, root, annotation),
                    work.levels,
                    work.names,
                    work.budget,
                )?;
            }
            Ok(root)
        })();
        let a = release(prefix, work.budget);
        let b = release(args, work.budget);
        let c = release(levels, work.budget);
        for cleanup in [a, b, c] {
            if let Err(error) = cleanup {
                work.record_nested_retirement(Err(error));
                return result.and(Err(error.into()));
            }
        }
        result
    }
}
fn raw_kind<'a>(root: ExprId, work: &'a mut Working<'_>) -> Result<ExprKind<'a>, Stop> {
    Ok(work
        .expressions
        .get(root, work.budget)?
        .kind(work.expressions, work.levels, work.budget)?)
}
