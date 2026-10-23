//! The ordinary checking dependency chain only: inference → head/comparison,
//! comparison → head, and K head → scoped type observation. Parents retain their
//! locals, lexical environments and caches. No driver call occurs inside advance.
use super::*;
mod finite;
mod head_cache;
mod immediate_head;
mod observation;
use crate::check::environment::normalization::{Head, full::comparison, machine as head};
use crate::syntax::levels::SharedMemo;

pub(super) enum Seed {
    Inference(ExprId, ReductionPath),
    Observation(crate::check::environment::normalization::TypeObservation),
    Head(ExprId, ReductionPath),
    CheapHead(ExprId, ReductionPath),
    NonDeltaHead(ExprId, ReductionPath),
    Comparison(ExprId, ExprId, ReductionPath),
}
#[derive(Clone, Copy)]
pub(super) enum Completed {
    Inference(Inferred),
    Observation(Inferred),
    Head(Head),
    // Only an exact completed cache hit with identical stored source/result IDs
    // mints this reply. It changes presentation, never reduction progress or
    // checkedness. It is consumed by the immediate parent, never cached/forwarded.
    UnchangedHead(Head),
    Comparison(comparison::Decision),
    Finite(finite::Reply),
}
const _: () = assert!(size_of::<Completed>() == 24);
enum Owner {
    Inference(machine::Machine),
    Observation(machine::Machine),
    Head(finite::GuardedHead, head_cache::Origin),
    Comparison(comparison::Machine),
    Finite(Vec<finite::State>),
    Vacant,
}
struct Job {
    owner: Owner,
    depth: usize,
}
// The largest owner stays comparison-sized in both builds. Its enum niche
// and the incoming depth keep semantic allocation at 240 bytes per job.
const _: () = assert!(size_of::<Job>() == 240);
enum Step {
    More,
    Need(Seed),
    Complete(Completed),
    FiniteMiss,
}

impl Job {
    fn new(
        seed: Seed,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<Self, Stop> {
        let depth = work.context.depth();
        let owner = match seed {
            Seed::Inference(root, path) => {
                Owner::Inference(machine::Machine::new(root, path, depth, work.budget)?)
            }
            Seed::Observation(request) => {
                Owner::Observation(machine::Machine::new_observation(request, work)?)
            }
            Seed::Head(root, path) => Owner::Head(
                finite::GuardedHead::new(head::Machine::new(
                    root,
                    path,
                    crate::check::environment::normalization::Exposure::Full,
                    work.budget,
                )?),
                head_cache::Origin::new(
                    root,
                    path,
                    crate::check::environment::normalization::Exposure::Full,
                ),
            ),
            Seed::NonDeltaHead(root, path) => Owner::Head(
                finite::GuardedHead::new(head::Machine::new(
                    root,
                    path,
                    crate::check::environment::normalization::Exposure::NonDelta,
                    work.budget,
                )?),
                head_cache::Origin::new(
                    root,
                    path,
                    crate::check::environment::normalization::Exposure::NonDelta,
                ),
            ),
            Seed::CheapHead(root, path) => Owner::Head(
                finite::GuardedHead::new(head::Machine::new(
                    root,
                    path,
                    crate::check::environment::normalization::Exposure::Cheap,
                    work.budget,
                )?),
                head_cache::Origin::new(
                    root,
                    path,
                    crate::check::environment::normalization::Exposure::Cheap,
                ),
            ),
            Seed::Comparison(left, right, path) => Owner::Comparison(comparison::Machine::new(
                left,
                right,
                path,
                scope,
                environment,
                work.budget,
            )?),
        };
        Ok(Self { owner, depth })
    }
    #[allow(clippy::too_many_arguments)]
    fn advance(
        &mut self,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
        templates: &mut crate::check::environment::instantiation::Cache,
        heads: &mut head_cache::Cache,
        plans: &mut crate::syntax::expressions::binding::plan::Cache,
        universes: &mut SharedMemo,
        prefix_trial: &mut comparison::PrefixTrial,
    ) -> Result<Step, Stop> {
        let step = match &mut self.owner {
            Owner::Inference(owner) => match owner.advance(work, scope, environment)? {
                machine::Demand::Head(inferred) => {
                    Step::Need(Seed::Head(inferred.ty, inferred.path))
                }
                machine::Demand::Comparison {
                    left,
                    right,
                    incoming,
                } => Step::Need(Seed::Comparison(left, right, incoming)),
                machine::Demand::Complete(inferred) => {
                    Step::Complete(Completed::Inference(inferred))
                }
            },
            Owner::Observation(owner) => {
                // A type observation is never checkedness or a fresh negative.
                // Keeping its result separate prevents reuse as checked inference.
                let demand = owner
                    .advance(work, scope, environment)
                    .map_err(observation_failure)?;
                match demand {
                    machine::Demand::Head(inferred) => {
                        Step::Need(Seed::Head(inferred.ty, inferred.path))
                    }
                    machine::Demand::Comparison { .. } => {
                        return Err(ResourceError::Invariant.into());
                    }
                    machine::Demand::Complete(observed) => {
                        Step::Complete(Completed::Observation(observed))
                    }
                }
            }
            Owner::Head(owner, _) => {
                if let Some(head) = owner.advance_with_plans(
                    scope,
                    environment,
                    work.expressions,
                    work.levels,
                    work.names,
                    work.context,
                    Some((templates, &mut work.caches)),
                    if scope.formation.is_none() {
                        Some(plans)
                    } else {
                        None
                    },
                    work.budget,
                )? {
                    Step::Complete(Completed::Head(head))
                } else if let Some((left, right, incoming)) = owner.comparison_request() {
                    // The head owner obtained computation metadata strictly from
                    // the committed frontier. run() fixes and validates the live
                    // phase and original frontiers; staged signatures never grant
                    // equations. Formation inference memoization stays disabled.
                    Step::Need(Seed::Comparison(left, right, incoming))
                } else if let Some(request) = owner.major_request() {
                    // The major belongs to the checked operand in this unchanged
                    // scope. Observation may read staged types, but only committed
                    // metadata can have created this computation demand.
                    Step::Need(Seed::Observation(request))
                } else {
                    Step::More
                }
            }
            Owner::Finite(owned) => owned.first_mut().ok_or(ResourceError::Invariant)?.advance(
                work,
                scope,
                environment,
                templates,
                heads,
                plans,
                universes,
            )?,
            Owner::Vacant => return Err(ResourceError::Invariant.into()),
            Owner::Comparison(owner) => match owner.advance_with_prefix(
                scope,
                environment,
                work.expressions,
                work.levels,
                work.names,
                work.context,
                &mut work.caches,
                work.budget,
                universes,
                prefix_trial,
            )? {
                comparison::Demand::Head { root, incoming } => {
                    Step::Need(Seed::Head(root, incoming))
                }
                comparison::Demand::NonDeltaHead { root, incoming } => {
                    Step::Need(Seed::NonDeltaHead(root, incoming))
                }
                comparison::Demand::CheapHead { root, incoming } => {
                    Step::Need(Seed::CheapHead(root, incoming))
                }
                comparison::Demand::Observation(request) => Step::Need(Seed::Observation(request)),
                comparison::Demand::Comparison {
                    left,
                    right,
                    incoming,
                } => Step::Need(Seed::Comparison(left, right, incoming)),
                comparison::Demand::Complete(path) => Step::Complete(Completed::Comparison(path)),
            },
        };
        Ok(step)
    }
    fn resume(
        &mut self,
        result: Completed,
        work: &mut Working<'_>,
        scope: &Scope<'_>,
        environment: &Environment,
    ) -> Result<(), Stop> {
        match (&mut self.owner, result) {
            (
                Owner::Inference(owner) | Owner::Observation(owner),
                Completed::Head(head) | Completed::UnchangedHead(head),
            ) => owner.resume_head(head),
            (Owner::Inference(owner), Completed::Comparison(comparison::Decision::Equal(path))) => {
                owner.resume_comparison(path)
            }
            (Owner::Inference(_), Completed::Comparison(comparison::Decision::Different(_))) => {
                Err(Stop::Judgment(Negative::TypeMismatch))
            }
            (Owner::Comparison(owner), Completed::Comparison(decision)) => {
                Ok(owner.resume_comparison(decision)?)
            }
            (Owner::Head(owner, _), Completed::Comparison(decision)) => {
                Ok(owner.resume_comparison(decision)?)
            }
            (Owner::Head(owner, _), Completed::Observation(inferred)) => {
                Ok(owner.resume_major(inferred.ty, inferred.path)?)
            }
            (Owner::Comparison(owner), Completed::Observation(observed)) => Ok(owner
                .resume_observation(Head {
                    expression: observed.ty,
                    path: observed.path,
                })?),
            (Owner::Comparison(owner), Completed::Head(head)) => Ok(owner.resume_head(head)?),
            (Owner::Comparison(owner), Completed::UnchangedHead(head)) => {
                Ok(owner.resume_unchanged_head(head)?)
            }
            (Owner::Finite(owned), result) => owned
                .first_mut()
                .ok_or(ResourceError::Invariant)?
                .resume(result, work, scope, environment),
            _ => Err(ResourceError::Invariant.into()),
        }
    }
    fn observation_boundary(&self) -> bool {
        match &self.owner {
            Owner::Observation(_) => true,
            Owner::Head(owner, _) => owner.observing_type(),
            Owner::Comparison(owner) => owner.observing_type(),
            _ => false,
        }
    }
    #[cfg(feature = "introspection")]
    fn diagnostic_snapshot(
        &self,
        work: &Working<'_>,
    ) -> Option<crate::report::failure_snapshot::Snapshot> {
        match &self.owner {
            Owner::Inference(owner) | Owner::Observation(owner) => owner.diagnostic_snapshot(work),
            Owner::Head(..) | Owner::Comparison(_) | Owner::Finite(_) | Owner::Vacant => None,
        }
    }
    /// `parent` is the job this one will resume, None for the inline root.
    fn optional_boundary(&self, parent: Option<&Job>) -> Option<OptionalBoundary> {
        match &self.owner {
            Owner::Finite(_) => Some(OptionalBoundary::Finite),
            Owner::Comparison(owner) if owner.optional_prefix() => Some(OptionalBoundary::Prefix),
            Owner::Comparison(owner) if owner.optional_general_structure() => {
                Some(OptionalBoundary::GeneralStructure)
            }
            Owner::Comparison(owner) if owner.optional_projection_comparison() => {
                Some(OptionalBoundary::Projection)
            }
            Owner::Comparison(owner) if owner.optional_same_definition() => {
                Some(OptionalBoundary::SameDefinition)
            }
            // Only a comparison parent can carry the positive-only restriction.
            // Inference would classify the head (expected Sort/Pi negatives);
            // observation would feed K/structure eligibility of an outer head.
            Owner::Head(owner, _)
                if owner.k_premise_pending()
                    && matches!(
                        parent,
                        Some(Job {
                            owner: Owner::Comparison(_),
                            ..
                        })
                    ) =>
            {
                Some(OptionalBoundary::KPremise)
            }
            _ => None,
        }
    }
    fn abandon(self, work: &mut Working<'_>) -> Result<(), Stop> {
        match self.owner {
            Owner::Inference(owner) | Owner::Observation(owner) => {
                owner.abandon(work.budget, &mut work.caches)
            }
            Owner::Head(owner, _) => Ok(owner.abandon(work.budget)?),
            Owner::Comparison(owner) => Ok(owner.abandon(&mut work.caches, work.budget)?),
            Owner::Finite(owned) => finite::retire(owned, work),
            Owner::Vacant => Err(ResourceError::Invariant.into()),
        }
    }
    fn retire(self, work: &mut Working<'_>) -> Result<(), Stop> {
        let result = match self.owner {
            Owner::Inference(owner) | Owner::Observation(owner) => {
                owner.retire(work.budget, &mut work.caches)
            }
            Owner::Head(owner, _) => Ok(owner.retire(work.budget)?),
            Owner::Comparison(owner) => Ok(owner.retire(&mut work.caches, work.budget)?),
            Owner::Finite(owned) => finite::retire(owned, work),
            Owner::Vacant => Err(ResourceError::Invariant.into()),
        };
        result?;
        Ok(())
    }
}

pub(super) fn locally_unsupported(error: Stop) -> bool {
    matches!(
        error,
        Stop::Unsupported
            | Stop::Inference(HeadError::Unsupported)
            | Stop::Normalization(HeadError::Unsupported)
            | Stop::Observation(HeadError::Unsupported)
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OptionalBoundary {
    Finite,
    SameDefinition,
    GeneralStructure,
    Projection,
    Prefix,
    /// A head owner waiting on its own K premise comparison whose parent is a
    /// comparison. Recovery: the parent becomes positive-only, then the head
    /// resumes ordinary iota on the original major without performing K.
    KPremise,
}

/// Chain positions (root first, active job excluded) of every optional boundary.
fn optional_boundaries<'a>(
    chain: impl Iterator<Item = &'a Job> + Clone,
) -> impl Iterator<Item = (usize, OptionalBoundary)> {
    chain
        .clone()
        .zip(std::iter::once(None).chain(chain.map(Some)))
        .enumerate()
        .filter_map(|(index, (job, parent))| {
            job.optional_boundary(parent).map(|kind| (index, kind))
        })
}

/// Error-only scan. An innermost independently positive same-definition or
/// general-C9 or projection boundary retains its own recovery. If the nearest
/// boundary is a prefix, preserve the existing oldest-prefix replay with prefix trials disabled;
/// that replay includes any intervening ordinary structure comparisons.
/// A K-premise head is a last resort: it is chosen (the nearest one) only when
/// no other boundary exists, where the error would otherwise escape the driver.
/// Every recovery available without it therefore keeps its route.
fn optional_recovery_target(
    boundaries: impl Iterator<Item = (usize, OptionalBoundary)>,
) -> Option<(usize, OptionalBoundary)> {
    let mut oldest_prefix = None;
    let mut nearest = None;
    let mut nearest_k = None;
    for (index, kind) in boundaries {
        if kind == OptionalBoundary::KPremise {
            nearest_k = Some((index, kind));
            continue;
        }
        if kind == OptionalBoundary::Prefix && oldest_prefix.is_none() {
            oldest_prefix = Some(index);
        }
        nearest = Some((index, kind));
    }
    match nearest {
        Some((_, OptionalBoundary::Prefix)) => oldest_prefix.map(|i| (i, OptionalBoundary::Prefix)),
        None => nearest_k,
        other => other,
    }
}

/// Error-only recovery, never a general failure-to-verdict adapter. All child
/// owners and caches die before their locals leave. The checkpoint belongs to
/// the immediate child, so binders opened by the surviving parent stay active.
fn abandon_optional_children(
    root: &mut Option<Job>,
    descendants: &mut Vec<Job>,
    target: usize,
    kind: OptionalBoundary,
    active_retired: &mut bool,
    work: &mut Working<'_>,
) -> Result<(), Stop> {
    // Chain index zero is the inline root. Descendant[target] is therefore
    // the immediate child of the surviving owner, including target == 0.
    let depth = descendants
        .get(target)
        .ok_or(ResourceError::Invariant)?
        .depth;
    *active_retired = true;
    descendants
        .pop()
        .ok_or(ResourceError::Invariant)?
        .abandon(work)?;
    while descendants.len() > target {
        let operation = descendants
            .pop()
            .ok_or(ResourceError::Invariant)?
            .abandon(work)
            .err();
        let frames = work.budget.release_frames(1).err().map(Stop::Resource);
        if let Some(error) = machine::select_failure([operation, frames, None, None]) {
            return Err(error);
        }
    }
    work.context.unwind_to(depth, work.budget)?;
    // The survivor is active before frame release/resume, exactly as for
    // ordinary child completion. Earlier errors leave its frame pending.
    *active_retired = false;
    work.budget.release_frames(1)?;
    if kind == OptionalBoundary::Finite {
        let Owner::Finite(owned) = &mut descendants
            .last_mut()
            .or(root.as_mut())
            .ok_or(ResourceError::Invariant)?
            .owner
        else {
            return Err(ResourceError::Invariant.into());
        };
        owned.first_mut().ok_or(ResourceError::Invariant)?.miss();
        return Ok(());
    }
    if kind == OptionalBoundary::KPremise {
        // The surviving head is never the inline root: its comparison parent
        // is the job below it. Restrict the parent before the head can resume
        // it; no reduction or path certificate is claimed for the premise.
        let (survivor, rest) = descendants
            .split_last_mut()
            .ok_or(ResourceError::Invariant)?;
        let (
            Some(Job {
                owner: Owner::Comparison(parent),
                ..
            }),
            Owner::Head(head, _),
        ) = (rest.last_mut().or(root.as_mut()), &mut survivor.owner)
        else {
            return Err(ResourceError::Invariant.into());
        };
        let forget = false;
        if !forget {
            parent.retain_unestablished_head()?;
        }
        head.resume_unestablished_k()?;
        return Ok(());
    }
    let Owner::Comparison(owner) = &mut descendants
        .last_mut()
        .or(root.as_mut())
        .ok_or(ResourceError::Invariant)?
        .owner
    else {
        return Err(ResourceError::Invariant.into());
    };
    owner.resume_inconclusive_shortcut()?;
    Ok(())
}

fn observation_failure(error: Stop) -> Stop {
    match error {
        Stop::Inference(error) | Stop::Normalization(error) => Stop::Observation(error),
        Stop::Judgment(_) | Stop::Scope(ScopeError::DuplicateParameter(_)) => {
            Stop::Resource(ResourceError::Invariant)
        }
        other => other,
    }
}

/// One outer Working poison owns this call. Scope, origins, environment and
/// permissions stay fixed; handles live until ordinary-session rollback. Every
/// child must restore its incoming context before retirement and parent resume.
/// The root job stays stack-owned; descendants occupy 240-byte vector slots.
/// Each nested request retains the same slot/frame charges and growth overlap.
/// A suspended parent stays in place across its child's execution.
#[allow(
    clippy::let_and_return,
    reason = "test-only observer omitted from public source"
)]
pub(super) fn run(
    seed: Seed,
    work: &mut Working<'_>,
    scope: &Scope<'_>,
    environment: &Environment,
) -> Result<Completed, Stop> {
    if scope.expression_end != work.original_expressions
        || scope.level_end != work.original_levels
        || environment
            .check_scope(
                scope.before,
                scope.formation,
                scope.expression_end,
                scope.level_end,
            )
            .is_err()
    {
        return Err(ResourceError::Invariant.into());
    }
    work.budget.charge_work(3)?; // flat cleanup: descendants, head cache, binding plans
    let mut descendants: Vec<Job> = Vec::new();
    let mut root = Some(Job::new(seed, work, scope, environment)?);
    let mut templates = crate::check::environment::instantiation::Cache::default();
    let mut heads = head_cache::Cache::default();
    let mut plans = crate::syntax::expressions::binding::plan::Cache::default();
    let mut comparison_epoch = 0u64;
    let mut prefix_trial = comparison::PrefixTrial::Enabled;
    // As amended: completed universe-normalization results shared by
    // every U request of this checking operation. Retired below with the other
    // optional tables, before the enclosing declaration reclaims level slots.
    let mut universes = SharedMemo::default();
    // Equivalent to the old current=None state after taking a failed retire.
    // It determines cleanup's frame releases and diagnostic ancestor bound only.
    let mut active_retired = false;
    let result = (|| loop {
        let request = match &descendants
            .last()
            .or(root.as_ref())
            .ok_or(ResourceError::Invariant)?
            .owner
        {
            Owner::Head(head, _) => head.candidate(work, scope, environment)?,
            _ => None,
        };
        if let Some(request) = request {
            work.budget.charge_work(descendants.len() as u64 + 1)?;
            let bank = finite::ancestor_bank(root.iter().chain(descendants.iter()), request.operands[1]);
            finite::begin(
                descendants
                    .last_mut()
                    .or(root.as_mut())
                    .ok_or(ResourceError::Invariant)?,
                request,
                bank,
                work,
                &mut templates,
                &mut heads,
                &mut plans,
                &mut universes,
            )?;
        }
        let job = descendants
            .last_mut()
            .or(root.as_mut())
            .ok_or(ResourceError::Invariant)?;
        let step = job.advance(
            work,
            scope,
            environment,
            &mut templates,
            &mut heads,
            &mut plans,
            &mut universes,
            &mut prefix_trial,
        );
        let step = step.map_err(|error| {
            if error.completed_negative().is_some() && root
                .iter()
                .chain(descendants.iter())
                .any(|job| matches!(job.owner, Owner::Finite(_)))
            {
                return Stop::Resource(ResourceError::Invariant);
            }
            // Error-only scan of precisely the active judgment and its ancestors.
            if root
                .iter()
                .chain(descendants.iter())
                .any(Job::observation_boundary)
            {
                observation_failure(error)
            } else {
                error
            }
        });
        let step = match step {
            Ok(step) => step,
            Err(error) if locally_unsupported(error) => {
                let Some((target, kind)) = optional_recovery_target(optional_boundaries(
                    root.iter()
                        .chain(descendants.iter())
                        .take(descendants.len()),
                )) else {
                    return Err(error);
                };
                if kind == OptionalBoundary::Prefix {
                    prefix_trial = comparison::PrefixTrial::Disabled;
                }
                abandon_optional_children(
                    &mut root,
                    &mut descendants,
                    target,
                    kind,
                    &mut active_retired,
                    work,
                )?;
                continue;
            }
            Err(error) => return Err(error),
        };
        match step {
            Step::Complete(Completed::Finite(reply)) => {
                finite::restore(
                    descendants
                        .last_mut()
                        .or(root.as_mut())
                        .ok_or(ResourceError::Invariant)?,
                    Some(reply),
                    work,
                    scope,
                    environment,
                    &mut templates,
                    &mut heads,
                    &mut plans,
                    &mut universes,
                )?;
            }
            Step::FiniteMiss => {
                finite::restore(
                    descendants
                        .last_mut()
                        .or(root.as_mut())
                        .ok_or(ResourceError::Invariant)?,
                    None,
                    work,
                    scope,
                    environment,
                    &mut templates,
                    &mut heads,
                    &mut plans,
                    &mut universes,
                )?;
            }
            Step::More => {}
            Step::Need(seed) => {
                if matches!(seed, Seed::Comparison(..)) {
                    comparison_epoch = comparison_epoch
                        .checked_add(1)
                        .ok_or(ResourceError::Counter)?;
                }
                let needed = descendants
                    .len()
                    .checked_add(1)
                    .ok_or(ResourceError::Counter)?;
                work.budget.reserve_frames(1)?;
                let growth = work.budget.grow_vec(&mut descendants, needed);
                if let Err(error) = growth {
                    work.budget.release_frames(1)?;
                    return Err(error.into());
                }
                if let Seed::Comparison(left, right, incoming) = seed
                    && left == right
                {
                    if let Err(error) = comparison::prepare_checked(scope, environment, work.budget)
                    {
                        work.budget.release_frames(1)?;
                        return Err(error.into());
                    }
                    // The omitted child owns no locals or cache. If C1 fails,
                    // its suspension frame still belongs to ancestor cleanup,
                    // exactly as after retiring an empty failed child owner.
                    active_retired = true;
                    let decision = {
                        let result = comparison::checked_identity(
                            left,
                            incoming,
                            work.expressions,
                            work.levels,
                            work.names,
                            work.budget,
                        );
                        result
                    }
                    .map_err(|error| {
                        let error = Stop::from(error);
                        if root
                            .iter()
                            .chain(descendants.iter())
                            .any(Job::observation_boundary)
                        {
                            observation_failure(error)
                        } else {
                            error
                        }
                    })?;
                    active_retired = false;
                    work.budget.release_frames(1)?;
                    let completed = Completed::Comparison(decision);
                    descendants
                        .last_mut()
                        .or(root.as_mut())
                        .ok_or(ResourceError::Invariant)?
                        .resume(completed, work, scope, environment)?;
                    continue;
                }
                if let Seed::Head(expression, incoming)
                | Seed::CheapHead(expression, incoming)
                | Seed::NonDeltaHead(expression, incoming) = seed
                {
                    // This omitted owner has no scratch or transported locals.
                    active_retired = true;
                    let exposed = immediate_head::complete(expression, incoming, work);
                    let exposed = exposed.map_err(|error| {
                        if root
                            .iter()
                            .chain(descendants.iter())
                            .any(Job::observation_boundary)
                        {
                            observation_failure(error)
                        } else {
                            error
                        }
                    })?;
                    let exposed = if exposed.is_none() && scope.formation.is_none() {
                        let exposure = match seed {
                            Seed::Head(..) => {
                                crate::check::environment::normalization::Exposure::Full
                            }
                            Seed::CheapHead(..) => {
                                crate::check::environment::normalization::Exposure::Cheap
                            }
                            _ => crate::check::environment::normalization::Exposure::NonDelta,
                        };
                        heads.get(expression, exposure, incoming, work)?
                    } else {
                        exposed.map(Completed::Head)
                    };
                    active_retired = false;
                    if let Some(exposed) = exposed {
                        work.budget.release_frames(1)?;
                        descendants
                            .last_mut()
                            .or(root.as_mut())
                            .ok_or(ResourceError::Invariant)?
                            .resume(exposed, work, scope, environment)?;
                        continue;
                    }
                }
                if let Seed::Observation(request) = seed {
                    // The omitted owner has no locals or scratch. On failure its
                    // suspension frame belongs to ancestor cleanup, as for C1.
                    active_retired = true;
                    let observed = observation::complete(request, work);
                    let observed = observed.map_err(observation_failure)?;
                    active_retired = false;
                    if let Some(observed) = observed {
                        work.budget.release_frames(1)?;
                        descendants
                            .last_mut()
                            .or(root.as_mut())
                            .ok_or(ResourceError::Invariant)?
                            .resume(Completed::Observation(observed), work, scope, environment)?;
                        continue;
                    }
                }
                let mut child = match Job::new(seed, work, scope, environment) {
                    Ok(child) => child,
                    Err(error) => {
                        work.budget.release_frames(1)?;
                        return Err(error);
                    }
                };
                if let Owner::Head(_, origin) = &mut child.owner {
                    origin.epoch = comparison_epoch;
                }
                if root
                    .iter()
                    .chain(descendants.iter())
                    .any(|job| matches!(job.owner, Owner::Observation(_)))
                    && let Owner::Head(head, _) = &mut child.owner
                {
                    head.observe();
                }
                descendants.push(child);
            }
            Step::Complete(completed) => {
                let job = descendants
                    .last()
                    .or(root.as_ref())
                    .ok_or(ResourceError::Invariant)?;
                if work.context.depth() != job.depth {
                    return Err(ResourceError::Invariant.into());
                }
                // A head whose K premise was never decided is a valid reduct,
                // not an established weak head. Its premise comparison already
                // advanced the epoch; the explicit test keeps it out of the head
                // cache without relying on that, and only a positive-only
                // comparison parent may receive it.
                let unestablished =
                    matches!(&job.owner, Owner::Head(head, _) if head.k_unestablished());
                let candidate = if scope.formation.is_none() && !unestablished {
                    match (&job.owner, completed) {
                        (Owner::Head(_, origin), Completed::Head(result)) => {
                            // Completed::Head came from successful advance; the
                            // origin record alone grants no completion authority.
                            if let Some((source, incoming, exposure)) =
                                origin.request(comparison_epoch)
                                && head_cache::closed(source, work.expressions, work.budget)?
                                && head_cache::closed(
                                    result.expression,
                                    work.expressions,
                                    work.budget,
                                )?
                            {
                                Some(head_cache::Candidate {
                                    source,
                                    result: result.expression,
                                    height: result.path.height_since(incoming)?,
                                    exposure,
                                })
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                };
                let child = descendants.pop();
                active_retired = true;
                if let Some(child) = child {
                    child.retire(work)?;
                    if let Some(candidate) = candidate {
                        heads.insert(candidate, work)?;
                    }
                    // The parent is now current, including if frame release or
                    // resume fails. Preserve the old cleanup release ordering.
                    active_retired = false;
                    work.budget.release_frames(1)?;
                    let parent = descendants
                        .last_mut()
                        .or(root.as_mut())
                        .ok_or(ResourceError::Invariant)?;
                    if unestablished
                        && !matches!(&parent.owner, Owner::Comparison(owner) if owner.positive_only())
                    {
                        return Err(ResourceError::Invariant.into());
                    }
                    parent.resume(completed, work, scope, environment)?;
                } else {
                    if unestablished {
                        return Err(ResourceError::Invariant.into());
                    }
                    root.take().ok_or(ResourceError::Invariant)?.retire(work)?;
                    if let Some(candidate) = candidate {
                        heads.insert(candidate, work)?;
                    }
                    return Ok(completed);
                }
            }
        }
    })().map_err(|error| {
        // Includes errors from child resumption and immediate completion, not
        // only advance(). No generated judgment can reject the original input.
        if error.completed_negative().is_some()
            && root.iter().chain(descendants.iter()).any(|job|matches!(job.owner,Owner::Finite(_)))
        {
            Stop::Resource(ResourceError::Invariant)
        } else { error }
    });
    #[cfg(feature = "introspection")]
    if result.is_err() && std::env::var_os("KEFIR_COLIMIT_PROBE").is_some() {
        eprintln!(
            "COLIMIT STOP {:?} before={} depth={}",
            result.as_ref().err(),
            scope.before,
            work.context.depth()
        );
        for job in root.iter().chain(descendants.iter()).rev().take(12) {
            match &job.owner {
                Owner::Comparison(owner) => {
                    owner.colimit_probe(crate::check::diagnostic::Sources {
                        expressions: work.expressions,
                        levels: work.levels,
                        names: work.names,
                        locals: Some(work.context),
                    })
                }
                Owner::Head(..) => eprintln!("COLIMIT H"),
                Owner::Observation(..) => eprintln!("COLIMIT O"),
                Owner::Inference(..) => eprintln!("COLIMIT I"),
                Owner::Finite(..) => eprintln!("COLIMIT F"),
                Owner::Vacant => eprintln!("COLIMIT unavailable owner"),
            }
        }
    }
    #[cfg(feature = "introspection")]
    let operation_failure = result.as_ref().err().copied();
    #[cfg(feature = "introspection")]
    let delayed_snapshot = operation_failure.map(|_| {
        const DIAGNOSTIC_PARENTS: usize = 12;
        descendants
            .iter()
            .rev()
            .chain(root.iter())
            .take(DIAGNOSTIC_PARENTS + usize::from(!active_retired))
            .find_map(|job| job.diagnostic_snapshot(work))
            .unwrap_or_else(crate::report::failure_snapshot::Snapshot::unavailable_delayed_context)
    });
    let mut failure = result.as_ref().err().copied();
    // With a live active owner, its retirement has no suspension frame to
    // release. Every following parent does. If the active owner already failed
    // retirement, start directly with a charged parent. This preserves error
    // priority and release timing even though different owners occupy the vector.
    let mut release_frame = active_retired;
    while let Some(job) = descendants.pop() {
        let retired = job.retire(work).err();
        let frame = if release_frame {
            work.budget.release_frames(1).err().map(Stop::Resource)
        } else {
            None
        };
        failure = machine::select_failure([failure, retired, frame, None]);
        release_frame = true;
    }
    if let Some(job) = root.take() {
        let retired = job.retire(work).err();
        let frame = if release_frame {
            work.budget.release_frames(1).err().map(Stop::Resource)
        } else {
            None
        };
        failure = machine::select_failure([failure, retired, frame, None]);
    }
    // Completed body/head results carry no term locals. Binding plans may retain
    // raw Free syntax but no local-validity answers or replacement values. Retire
    // every table before the outer declaration can reclaim generated syntax.
    failure = machine::select_failure([
        failure,
        templates
            .retire(&mut work.caches, work.budget)
            .err()
            .map(Stop::Resource),
        heads.retire(work).err().map(Stop::Resource),
        plans
            .retire(&mut work.caches, work.budget)
            .err()
            .map(Stop::Resource),
        universes
            .retire(&mut work.caches, work.budget)
            .err()
            .map(Stop::Resource),
    ]);
    let bytes = descendants
        .capacity()
        .checked_mul(size_of::<Job>())
        .ok_or(ResourceError::Counter);
    drop(descendants);
    failure = machine::select_failure([
        failure,
        bytes
            .and_then(|bytes| work.budget.release(bytes as u64))
            .err()
            .map(Stop::Resource),
        None,
        None,
    ]);
    #[cfg(feature = "introspection")]
    if failure == operation_failure
        && let Some(snapshot) = delayed_snapshot
    {
        work.budget.capture_failure(snapshot);
    }
    match failure {
        Some(error) => Err(error),
        None => result,
    }
}
