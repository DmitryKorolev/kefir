//! Whole-block admission plan. This index owns no checkedness or computation authority.
use super::*;
use crate::decode::primitive_decode::ordinary_session::Negative;

#[derive(Clone, Copy)]
struct Entry {
    canonical: u32,
    kind: u32, // family=0, constructor=1, recursor=2
    position: u32,
}
const _: () = assert!(std::mem::size_of::<Entry>() == 12);
#[derive(Default)]
struct Plan {
    entries: Vec<Entry>,
    constructors: Vec<u32>,
    recursors: Vec<u32>,
    indices: Vec<u32>,
}
fn mismatch() -> Stop {
    Stop::Judgment(Negative::TypeMismatch)
}
impl Plan {
    fn find(
        &self,
        name: NameId,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Option<Entry>, Stop> {
        budget.charge_work(u64::from(self.entries.len().checked_ilog2().unwrap_or(0)) + 1)?;
        let canonical = names.summary(name, budget)?.canonical;
        Ok(self
            .entries
            .binary_search_by_key(&canonical, |e| e.canonical)
            .ok()
            .map(|i| self.entries[i]))
    }
    fn fill(&mut self, work: &mut Working<'_>, request: &Request<'_>) -> Result<(), Stop> {
        let first = request.types.first().ok_or(Stop::Unsupported)?;
        // Unsafe and nested groups remain outside this admission slice, including
        // malformed metadata on such groups. Neither is a negative rule.
        if request
            .types
            .iter()
            .any(|f| f.is_unsafe || f.num_nested != 0)
            || request.constructors.iter().any(|c| c.is_unsafe)
            || request.recursors.iter().any(|r| r.is_unsafe)
        {
            return Err(Stop::Unsupported);
        }
        if request.recursors.len() != request.types.len()
            || request.rules.len() != request.constructors.len()
        {
            return Err(mismatch());
        }
        let total = request
            .types
            .len()
            .checked_add(request.constructors.len())
            .and_then(|n| n.checked_add(request.recursors.len()))
            .ok_or(ResourceError::Counter)?;
        work.budget.grow_vec(&mut self.entries, total)?;
        for (kind, position, name) in request
            .types
            .iter()
            .enumerate()
            .map(|(i, f)| (0, i, f.name))
            .chain(
                request
                    .constructors
                    .iter()
                    .enumerate()
                    .map(|(i, c)| (1, i, c.name)),
            )
            .chain(
                request
                    .recursors
                    .iter()
                    .enumerate()
                    .map(|(i, r)| (2, i, r.name)),
            )
        {
            self.entries.push(Entry {
                canonical: work.names.summary(name, work.budget)?.canonical,
                kind,
                position: u32::try_from(position).map_err(|_| ResourceError::Counter)?,
            });
        }
        work.budget.charge_work(
            (total as u64)
                .checked_mul(u64::from(total.checked_ilog2().unwrap_or(0)) + 2)
                .ok_or(ResourceError::Counter)?,
        )?;
        self.entries.sort_unstable_by_key(|e| e.canonical);
        if self
            .entries
            .windows(2)
            .any(|e| e[0].canonical == e[1].canonical)
        {
            return Err(mismatch());
        }
        work.budget
            .grow_vec(&mut self.recursors, request.types.len())?;
        self.recursors.resize(request.types.len(), u32::MAX);
        work.budget
            .grow_vec(&mut self.indices, request.types.len())?;
        self.indices.resize(request.types.len(), 0);
        let parameters = list(request.names, first.parameters)?;
        let mut rule_end = 0usize;
        for (position, recursor) in request.recursors.iter().enumerate() {
            let Some((owner, Component::String("rec"))) =
                work.names.view(recursor.name, work.budget)?
            else {
                return Err(mismatch());
            };
            let Some(entry) = self.find(owner, work.names, work.budget)? else {
                return Err(mismatch());
            };
            if entry.kind != 0 || self.recursors[entry.position as usize] != u32::MAX {
                return Err(mismatch());
            }
            self.recursors[entry.position as usize] =
                u32::try_from(position).map_err(|_| ResourceError::Counter)?;
            if recursor.rules.start as usize != rule_end {
                return Err(mismatch());
            }
            rule_end = rule_end
                .checked_add(recursor.rules.len as usize)
                .ok_or(ResourceError::Counter)?;
        }
        if rule_end != request.rules.len() {
            return Err(mismatch());
        }
        // The specification lists, not serialized ownership fields, define the
        // partition. A sorted temporary membership list detects repeated owners.
        let mut used = Vec::new();
        let result = (|| {
            work.budget
                .grow_vec(&mut used, request.constructors.len())?;
            for (member, family) in request.types.iter().enumerate() {
                if family.num_params != first.num_params
                    || !parameters_equal(
                        work.names,
                        parameters,
                        list(request.names, family.parameters)?,
                        work.budget,
                    )?
                {
                    return Err(mismatch());
                }
                let all = list(request.names, family.all)?;
                if all.len() != request.types.len() {
                    return Err(mismatch());
                }
                for (&name, expected) in all.iter().zip(request.types) {
                    if !same(work.names, name, expected.name, work.budget)? {
                        return Err(mismatch());
                    }
                }
                let recursor = &request.recursors[self.recursors[member] as usize];
                if !parameters_equal(
                    work.names,
                    all,
                    list(request.names, recursor.all)?,
                    work.budget,
                )? || recursor.num_params != first.num_params
                    || recursor.num_motives as usize != request.types.len()
                    || recursor.num_minors as usize != request.constructors.len()
                    || recursor.k
                {
                    return Err(mismatch());
                }
                let constructors = list(request.names, family.constructors)?;
                if recursor.rules.len as usize != constructors.len() {
                    return Err(mismatch());
                }
                for (position, &name) in constructors.iter().enumerate() {
                    let Some(entry) = self.find(name, work.names, work.budget)? else {
                        return Err(mismatch());
                    };
                    if entry.kind != 1 {
                        return Err(mismatch());
                    }
                    let c = &request.constructors[entry.position as usize];
                    if !same(work.names, c.inductive, family.name, work.budget)?
                        || c.index as usize != position
                        || c.num_params != first.num_params
                        || !parameters_equal(
                            work.names,
                            parameters,
                            list(request.names, c.parameters)?,
                            work.budget,
                        )?
                    {
                        return Err(mismatch());
                    }
                    scheme::push(work, &mut self.constructors, entry.position)?;
                    scheme::push(work, &mut used, entry.position)?;
                }
            }
            if used.len() != request.constructors.len() {
                return Err(mismatch());
            }
            work.budget.charge_work(
                (used.len() as u64)
                    .checked_mul(u64::from(used.len().checked_ilog2().unwrap_or(0)) + 2)
                    .ok_or(ResourceError::Counter)?,
            )?;
            used.sort_unstable();
            if used
                .iter()
                .enumerate()
                .any(|(i, &actual)| i != actual as usize)
            {
                return Err(mismatch());
            }
            Ok(())
        })();
        let bytes = used.capacity() * std::mem::size_of::<u32>();
        drop(used);
        work.budget.release(bytes as u64)?;
        result
    }
    fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        let bytes = self.entries.capacity() * std::mem::size_of::<Entry>()
            + (self.constructors.capacity() + self.recursors.capacity() + self.indices.capacity())
                * 4;
        drop(self);
        budget.release(bytes as u64)
    }
}

impl State {
    pub(super) fn check_mutual(
        &mut self,
        request: &Request<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
    ) -> Result<Admission, FailureReport> {
        let mut plan = Plan::default();
        let mut rules = Vec::new();
        let result = self.mutual_inner(request, ordinal, decoder, budget, &mut plan, &mut rules);
        let bytes = rules.capacity() * std::mem::size_of::<NullaryRule>();
        drop(rules);
        let release = budget.release(bytes as u64);
        plan.retire(budget).map_err(ResourceError::failure_report)?;
        release.map_err(ResourceError::failure_report)?;
        result
    }
    fn mutual_inner(
        &mut self,
        request: &Request<'_>,
        ordinal: u64,
        decoder: &mut Decoder,
        budget: &mut Budget,
        plan: &mut Plan,
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
        if decoder
            .declaration_session(budget, |work| plan.fill(work, request))
            .map_err(|e| e.failure_report())?
            .is_some()
        {
            return Ok(Admission::TypeMismatch);
        }
        let first = &request.types[0];
        let parameters = list(request.names, first.parameters).map_err(resource)?;
        let rec_parameters = list(
            request.names,
            request.recursors[plan.recursors[0] as usize].parameters,
        )
        .map_err(resource)?;
        let before = self.environment.len();
        for name in request
            .types
            .iter()
            .map(|f| f.name)
            .chain(request.constructors.iter().map(|c| c.name))
            .chain(request.recursors.iter().map(|r| r.name))
        {
            if self
                .environment
                .lookup(name, before, decoder.syntax().0, budget)
                .map_err(resource)?
                .is_some()
            {
                return Ok(Admission::Duplicate);
            }
        }
        let expression_end = decoder.syntax().2.len();
        let level_end = decoder.syntax().1.len();
        let scope = |formation: Option<Formation>, parameters| Scope {
            parameters,
            before: formation.map_or(before, |p| p.before()),
            mode: Mode::Safe,
            expression_end,
            level_end,
            formation,
        };
        let mut valid = true;
        let mut positive = LevelPositive::NotProven;
        let negative = decoder
            .declaration_session(budget, |work| {
                families::with_set(
                    work,
                    request.types.iter().map(|f| f.name),
                    |work, members| {
                        let mut offset = 0;
                        for family in request.types {
                            work.check_root_scope(parameters, &[family.ty])?;
                            for _ in list(request.names, family.constructors)? {
                                let constructor =
                                    &request.constructors[plan.constructors[offset] as usize];
                                offset += 1;
                                work.check_root_scope(parameters, &[constructor.ty])?;
                                if !raw_constructor(
                                    work,
                                    family,
                                    members,
                                    request.types,
                                    parameters,
                                    constructor.ty,
                                )? {
                                    valid = false;
                                    return Ok(());
                                }
                            }
                        }
                        Ok(())
                    },
                )?;
                if !valid {
                    return Ok(());
                }
                with_scratch(work, |work, s| {
                    // Pre-staging authority: committed environment only;
                    // the staged pass below re-types the same family.
                    work.with_pre_staging_sorts(|work| {
                        s.family(work, request, scope(None, parameters), &self.environment)
                    })?;
                    positive = work
                        .levels
                        .get(s.result.ok_or(ResourceError::Invariant)?, work.budget)?
                        .positive();
                    for (member, family) in request.types.iter().enumerate() {
                        let count = s.family_indices(member)?;
                        plan.indices[member] = count;
                        if family.num_indices != count
                            || request.recursors[plan.recursors[member] as usize].num_indices
                                != count
                        {
                            valid = false;
                        }
                    }
                    Ok(())
                })
            })
            .map_err(|e| e.failure_report())?;
        if negative.is_some() || !valid {
            return Ok(Admission::TypeMismatch);
        }
        // Multi-member groups never gain singleton elimination or K authority.
        // Direction of use: Proven selects the recursor
        // universe shape; NotProven contributes nothing and selects the plain
        // shape below without a negative conclusion.
        let universe = if positive == LevelPositive::Proven {
            if rec_parameters.len() != parameters.len() + 1
                || !parameters_equal(decoder.syntax().0, &rec_parameters[1..], parameters, budget)
                    .map_err(resource)?
                || !fresh_parameter(decoder.syntax().0, parameters, rec_parameters[0], budget)
                    .map_err(resource)?
            {
                return Ok(Admission::TypeMismatch);
            }
            Some(rec_parameters[0])
        } else {
            if !parameters_equal(decoder.syntax().0, rec_parameters, parameters, budget)
                .map_err(resource)?
            {
                return Ok(Admission::TypeMismatch);
            }
            None
        };
        for recursor in request.recursors {
            if !parameters_equal(
                decoder.syntax().0,
                rec_parameters,
                list(request.names, recursor.parameters).map_err(resource)?,
                budget,
            )
            .map_err(resource)?
            {
                return Ok(Admission::TypeMismatch);
            }
        }
        let mut phase = self
            .environment
            .begin_stage(expression_end, level_end, budget)
            .map_err(resource)?;
        for family in request.types {
            phase = self
                .environment
                .stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Inductive,
                        name: family.name,
                        parameters,
                        ty: family.ty,
                        all: list(request.names, family.all).map_err(resource)?,
                    },
                    decoder.syntax().0,
                    budget,
                )
                .map_err(resource)?;
        }
        let mut recursive = false;
        let negative = decoder
            .declaration_session(budget, |work| {
                with_scratch(work, |work, s| {
                    let scope = scope(Some(phase), parameters);
                    s.family(work, request, scope, &self.environment)?;
                    if !s.constructors(work, request, scope, &self.environment)? {
                        valid = false;
                        return Ok(());
                    }
                    recursive = s.recursive;
                    if request
                        .types
                        .iter()
                        .any(|f| f.is_recursive != s.recursive || f.is_reflexive != s.reflexive)
                    {
                        valid = false;
                        return Ok(());
                    }
                    let mut offset = 0;
                    for (member, family) in request.types.iter().enumerate() {
                        let recursor = &request.recursors[plan.recursors[member] as usize];
                        for (local, &name) in
                            list(request.names, family.constructors)?.iter().enumerate()
                        {
                            let c = &request.constructors[plan.constructors[offset] as usize];
                            let rule = &request.rules[recursor.rules.start as usize + local];
                            let fields = s.field_count(offset)?;
                            if c.num_fields != fields
                                || rule.num_fields != fields
                                || !same(work.names, rule.constructor, name, work.budget)?
                            {
                                valid = false;
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
                            offset += 1;
                        }
                    }
                    Ok(())
                })
            })
            .map_err(|e| e.failure_report())?;
        if negative.is_some() || !valid {
            return Ok(Admission::TypeMismatch);
        }
        let all = list(request.names, first.all).map_err(resource)?;
        for &index in &plan.constructors {
            let c = &request.constructors[index as usize];
            phase = self
                .environment
                .stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Constructor,
                        name: c.name,
                        parameters,
                        ty: c.ty,
                        all,
                    },
                    decoder.syntax().0,
                    budget,
                )
                .map_err(resource)?;
        }
        let negative = decoder
            .declaration_session(budget, |work| {
                with_scratch(work, |work, s| {
                    let scope = scope(Some(phase), rec_parameters);
                    s.family(work, request, scope, &self.environment)?;
                    if !s.constructors(work, request, scope, &self.environment)? {
                        return Err(ResourceError::Invariant.into());
                    }
                    s.add_motives(work, universe, scope, &self.environment)?;
                    for (member, family) in request.types.iter().enumerate() {
                        let generated = s.recursor(work, family.name)?;
                        work.check_root_scope(rec_parameters, &[generated])?;
                        work.check_type(
                            generated,
                            false,
                            ReductionPath::start(),
                            scope,
                            &self.environment,
                        )?;
                        if !scheme::matches(
                            work,
                            generated,
                            request.recursors[plan.recursors[member] as usize].ty,
                        )? {
                            valid = false;
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
        if !valid {
            return Ok(Admission::TypeMismatch);
        }
        for &index in &plan.recursors {
            let r = &request.recursors[index as usize];
            phase = self
                .environment
                .stage_signature(
                    phase,
                    SignatureInput {
                        kind: SignatureKind::Recursor,
                        name: r.name,
                        parameters: rec_parameters,
                        ty: r.ty,
                        all,
                    },
                    decoder.syntax().0,
                    budget,
                )
                .map_err(resource)?;
        }
        let negative = decoder
            .declaration_session(budget, |work| {
                with_scratch(work, |work, s| {
                    let scope = scope(Some(phase), rec_parameters);
                    s.family(work, request, scope, &self.environment)?;
                    if !s.constructors(work, request, scope, &self.environment)? {
                        return Err(ResourceError::Invariant.into());
                    }
                    s.add_motives(work, universe, scope, &self.environment)?;
                    let mut offset = 0;
                    for (member, family) in request.types.iter().enumerate() {
                        let recursor = &request.recursors[plan.recursors[member] as usize];
                        for _ in list(request.names, family.constructors)? {
                            let generated = s.rhs(work, recursor.name, offset)?;
                            work.check_root_scope(rec_parameters, &[generated])?;
                            s.recheck(work, generated, offset, scope, &self.environment)?;
                            if !scheme::matches(work, generated, rules[offset].rhs)? {
                                valid = false;
                                return Ok(());
                            }
                            offset += 1;
                        }
                    }
                    Ok(())
                })
            })
            .map_err(|e| e.failure_report())?;
        if negative.is_some() {
            return Err(resource(ResourceError::Invariant));
        }
        if !valid {
            return Ok(Admission::TypeMismatch);
        }
        let mut metadata = Vec::new();
        // All slices refer only to original decoded rules; generated syntax has
        // already retired. Preflight reserves the whole block before any append.
        let result = (|| {
            budget
                .grow_vec(&mut metadata, request.types.len())
                .map_err(resource)?;
            let mut offset = 0;
            for (member, family) in request.types.iter().enumerate() {
                let count = family.constructors.len as usize;
                metadata.push(NullaryMetadata {
                    family: family.name,
                    recursor: request.recursors[plan.recursors[member] as usize].name,
                    k: false,
                    nonrecursive: !recursive,
                    num_params: first.num_params,
                    num_indices: plan.indices[member],
                    rules: &rules[offset..offset + count],
                });
                offset += count;
            }
            self.environment
                .prepare_inductive_commit(phase, &metadata, decoder.syntax().0, budget)
                .map_err(resource)?
                .commit();
            Ok(())
        })();
        let bytes = metadata.capacity() * std::mem::size_of::<NullaryMetadata<'_>>();
        drop(metadata);
        budget.release(bytes as u64).map_err(resource)?;
        result?;
        self.checked = next;
        budget.checked_declarations(next);
        budget.observe(Event::DeclarationsInstalled, plan.entries.len() as u64);
        Ok(Admission::Installed)
    }
}
