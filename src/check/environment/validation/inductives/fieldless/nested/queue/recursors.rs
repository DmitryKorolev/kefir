//! Independently derived/rechecked recursor types and RHSs for the expanded
//! mutual block. No metadata, restoration proof or admission is produced.
use super::super::super::scheme::Templates;
use super::*;
use crate::check::environment::SignatureStageCheckpoint;

#[derive(Clone, Copy)]
pub(super) struct Recursor {
    pub name: NameId,
    pub ty: ExprId,
    pub indices: u32,
    pub rules: u32,
}
#[derive(Clone, Copy)]
pub(super) struct Rule {
    pub constructor: NameId,
    pub fields: u32,
    pub rhs: ExprId,
    pub ty: ExprId,
}
const _: () = assert!(size_of::<Recursor>() == 16);
const _: () = assert!(size_of::<Rule>() == 16);
#[derive(Default)]
pub(super) struct Derived {
    pub types: Vec<Recursor>,
    pub rules: Vec<Rule>,
    pub exported: Vec<u32>,
    pub phase: Option<Formation>,
    pub checkpoint: Option<SignatureStageCheckpoint>,
    pub recursive: bool,
    pub reflexive: bool,
}
impl Derived {
    pub(super) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        release(self.types, budget)?;
        release(self.rules, budget)?;
        release(self.exported, budget)
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn derive(
    expanded: &expanded::Expanded<'_, '_>,
    request: &Request<'_>,
    scratch: &mut scheme::Scratch,
    work: &mut Working<'_>,
    environment: &mut Environment,
    scope: Scope<'_>,
    checkpoint: SignatureStageCheckpoint,
    output: &mut Derived,
) -> Result<(), Stop> {
    if expanded.family_count() < 2 {
        // Singleton elimination requires its own derivation; the expanded
        // multi-family rule cannot manufacture that authority.
        return Err(Stop::Unsupported);
    }
    let first = expanded.family(0)?;
    let mut primary = None;
    for recursor in request.recursors {
        if let Some((owner, Component::String("rec"))) =
            work.names.view(recursor.name, work.budget)?
            && same(work.names, owner, first.name, work.budget)?
            && primary.replace(recursor).is_some()
        {
            return Err(Stop::Unsupported);
        }
    }
    let parameters = list(request.names, primary.ok_or(Stop::Unsupported)?.parameters)?;
    let positive = work
        .levels
        .get(scratch.result.ok_or(ResourceError::Invariant)?, work.budget)?
        .positive();
    // Direction of use: Proven selects the recursor
    // universe shape; NotProven contributes nothing and selects the plain
    // shape below without a negative conclusion.
    let universe = if positive == LevelPositive::Proven {
        if parameters.len() != first.parameters.len() + 1
            || !parameters_equal(work.names, &parameters[1..], first.parameters, work.budget)?
            || !fresh_parameter(work.names, first.parameters, parameters[0], work.budget)?
        {
            return Err(Stop::Unsupported);
        }
        Some(parameters[0])
    } else {
        if !parameters_equal(work.names, parameters, first.parameters, work.budget)? {
            return Err(Stop::Unsupported);
        }
        None
    };
    let mut members = Vec::new();
    if !output.types.is_empty() || !output.rules.is_empty() || output.phase.is_some() {
        return Err(ResourceError::Invariant.into());
    }
    let result = (|| {
        for name in expanded.family_names() {
            push(&mut members, name, work.budget)?;
        }
        let mut phase = scope.formation.ok_or(ResourceError::Invariant)?;
        for member in 0..expanded.family_count() {
            let family = expanded.family(member)?;
            for index in 0..family.constructors {
                let constructor = expanded.constructor(member, index, work)?;
                // Original as well as helper names must remain unoccupied;
                // there is no justified public collision rule in this slice.
                if environment
                    .lookup_visible(
                        constructor.name,
                        phase.before(),
                        Some(phase),
                        work.names,
                        work.budget,
                    )?
                    .is_some()
                {
                    return Err(Stop::Unsupported);
                }
                phase = environment.stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Constructor,
                        name: constructor.name,
                        parameters: first.parameters,
                        ty: constructor.ty,
                        all: &members,
                    },
                    work.names,
                    work.budget,
                )?;
            }
        }
        let scope = Scope {
            formation: Some(phase),
            before: phase.before(),
            parameters,
            ..scope
        };
        scratch.add_motives(work, universe, scope, environment)?;
        output.recursive = scratch.recursive;
        output.reflexive = scratch.reflexive;
        for (member, name) in expanded.family_names().enumerate() {
            let recursor = work
                .names
                .append(name, Component::String("rec"), work.budget)
                .map_err(|error| match error {
                    crate::syntax::names::NameError::Resource(error) => Stop::Resource(error),
                    _ => Stop::Resource(ResourceError::Invariant),
                })?;
            if environment
                .lookup_visible(
                    recursor,
                    phase.before(),
                    Some(phase),
                    work.names,
                    work.budget,
                )?
                .is_some()
            {
                return Err(Stop::Unsupported);
            }
            let ty = scratch.recursor(work, name)?;
            work.check_root_scope(parameters, &[ty])?;
            work.check_type(ty, false, ReductionPath::start(), scope, environment)?;
            scratch.set_recursor(work, name, recursor)?;
            push(
                &mut output.types,
                Recursor {
                    name: recursor,
                    ty,
                    indices: scratch.family_indices(member)?,
                    rules: u32::try_from(expanded.family(member)?.constructors)
                        .map_err(|_| ResourceError::Counter)?,
                },
                work.budget,
            )?;
        }
        // Every generated type is now checked. Retire the old capability before
        // freezing a new template pool; never stretch the earlier numeric bound.
        environment.retire_signature_stage(checkpoint, phase, work.names, work.budget)?;
        // Existing checked locals retain their exact type handles. No inference
        // occurs in the gap; the next phase restores the identical checked
        // family/constructor prefix before adding any recursor signatures.
        output.checkpoint = Some(environment.signature_stage_checkpoint()?);
        phase = environment.begin_auxiliary_stage(
            scope.expression_end,
            scope.level_end,
            work.expressions,
            work.levels,
            work.budget,
        )?;
        for member in 0..expanded.family_count() {
            let family = expanded.family(member)?;
            phase = environment.stage_signature(
                phase,
                SignatureInput {
                    kind: SignatureKind::Inductive,
                    name: family.name,
                    parameters: first.parameters,
                    ty: family.ty,
                    all: &members,
                },
                work.names,
                work.budget,
            )?;
        }
        for member in 0..expanded.family_count() {
            let family = expanded.family(member)?;
            for index in 0..family.constructors {
                let constructor = expanded.constructor(member, index, work)?;
                phase = environment.stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Constructor,
                        name: constructor.name,
                        parameters: first.parameters,
                        ty: constructor.ty,
                        all: &members,
                    },
                    work.names,
                    work.budget,
                )?;
            }
        }
        for &Recursor { name, ty, .. } in &output.types {
            phase = environment.stage_signature(
                phase,
                SignatureInput {
                    kind: SignatureKind::Recursor,
                    name,
                    parameters,
                    ty,
                    all: &members,
                },
                work.names,
                work.budget,
            )?;
        }
        let scope = Scope {
            before: phase.before(),
            formation: Some(phase),
            ..scope
        };
        let mut offset = 0usize;
        for (member, &Recursor { name: recursor, .. }) in output.types.iter().enumerate() {
            let family = expanded.family(member)?;
            for index in 0..family.constructors {
                let constructor = expanded.constructor(member, index, work)?;
                let rhs = scratch.rhs(work, recursor, offset)?;
                work.check_root_scope(parameters, &[rhs])?;
                scratch.recheck(work, rhs, offset, scope, environment)?;
                let ty = scratch.rule_type(work, offset)?;
                work.check_root_scope(parameters, &[ty])?;
                work.check_type(ty, false, ReductionPath::start(), scope, environment)?;
                push(
                    &mut output.rules,
                    Rule {
                        constructor: constructor.name,
                        fields: scratch.field_count(offset)?,
                        rhs,
                        ty,
                    },
                    work.budget,
                )?;
                offset = offset.checked_add(1).ok_or(ResourceError::Counter)?;
            }
        }
        output.phase = Some(phase);
        // Retained roots are still private. Exact restoration, restored type and
        // computation matching, and atomic public admission remain separate work.
        Ok(())
    })();
    release(members, work.budget)?;
    result
}
