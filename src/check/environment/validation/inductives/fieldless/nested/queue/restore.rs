//! Pure saved-key restoration. No checkedness crosses the private/public boundary.
//! These transformations confer no checkedness or computation authority.
use super::*;
use crate::syntax::levels::LevelKind;

pub(super) struct Restorer<'a> {
    queue: &'a Queue,
    parameters: &'a [NameId],
    term_parameters: u32,
    rows: Vec<(u32, u32)>, // canonical private name -> recipe ordinal
    public_recursors: Vec<NameId>,
}
impl<'a> Restorer<'a> {
    pub(super) fn new(queue: &'a Queue, parameters: &'a [NameId]) -> Self {
        Self {
            queue,
            parameters,
            term_parameters: 0,
            rows: Vec::new(),
            public_recursors: Vec::new(),
        }
    }
    pub(super) fn prepare(
        &mut self,
        first: NameId,
        request: &Request<'_>,
        work: &mut Working<'_>,
        environment: &Environment,
    ) -> Result<(), Stop> {
        if !self.rows.is_empty() || !self.public_recursors.is_empty() {
            return Err(ResourceError::Invariant.into());
        }
        if let Some(first) = request.types.first() {
            self.term_parameters = first.num_params;
        }
        for family in &self.queue.families {
            self.row(family.helper, work)?;
        }
        for ctor in &self.queue.constructors {
            self.row(ctor.helper, work)?;
        }
        for (index, family) in self.queue.families.iter().enumerate() {
            let ordinal = u32::try_from(index)
                .map_err(|_| ResourceError::Counter)?
                .checked_add(1)
                .ok_or(ResourceError::Counter)?;
            let public = public_recursor(first, ordinal, work)?;
            if environment
                .lookup(public, environment.len(), work.names, work.budget)?
                .is_some()
            {
                return Err(Stop::Unsupported);
            }
            // Public recursor rows are expected in the request; family/constructor
            // collisions are not. No free-suffix search changes the public name.
            for name in request
                .types
                .iter()
                .map(|f| f.name)
                .chain(request.constructors.iter().map(|c| c.name))
            {
                if same(work.names, name, public, work.budget)? {
                    return Err(Stop::Unsupported);
                }
            }
            push(&mut self.public_recursors, public, work.budget)?;
            let private = work
                .names
                .append(family.helper, Component::String("rec"), work.budget)
                .map_err(name_error)?;
            self.row(private, work)?;
        }
        let count = self.rows.len();
        work.budget.charge_work(
            (count as u64)
                .checked_mul(u64::from(count.checked_ilog2().unwrap_or(0)) + 2)
                .ok_or(ResourceError::Counter)?,
        )?;
        self.rows.sort_unstable_by_key(|row| row.0);
        if self.rows.windows(2).any(|rows| rows[0].0 == rows[1].0) {
            return Err(Stop::Unsupported);
        }
        Ok(())
    }
    fn row(&mut self, name: NameId, work: &mut Working<'_>) -> Result<(), Stop> {
        let key = work.names.summary(name, work.budget)?.canonical;
        let index = u32::try_from(self.rows.len()).map_err(|_| ResourceError::Counter)?;
        push(&mut self.rows, (key, index), work.budget)
    }
    fn find(&self, name: NameId, work: &mut Working<'_>) -> Result<Option<usize>, Stop> {
        let key = work.names.summary(name, work.budget)?.canonical;
        work.budget
            .charge_work(u64::from(self.rows.len().checked_ilog2().unwrap_or(0)) + 1)?;
        Ok(self
            .rows
            .binary_search_by_key(&key, |row| row.0)
            .ok()
            .map(|index| self.rows[index].1 as usize))
    }
    pub(super) fn recursor(&self, index: usize) -> Result<NameId, Stop> {
        self.public_recursors
            .get(index)
            .copied()
            .ok_or_else(|| ResourceError::Invariant.into())
    }
    pub(super) fn constructor(&self, name: NameId, work: &mut Working<'_>) -> Result<NameId, Stop> {
        let Some(index) = self.find(name, work)? else {
            return Ok(name);
        };
        let index = index
            .checked_sub(self.queue.families.len())
            .ok_or(ResourceError::Invariant)?;
        self.queue
            .constructors
            .get(index)
            .map(|c| c.prior)
            .ok_or_else(|| ResourceError::Invariant.into())
    }
    pub(super) fn root(&self, root: ExprId, work: &mut Working<'_>) -> Result<ExprId, Stop> {
        if work.expressions.get(root, work.budget)?.loose_range() != 0 {
            return Err(ResourceError::Invariant.into());
        }
        if self.term_parameters != 0 {
            return self.parameterized_root(root, work);
        }
        rewrite::walk(
            root,
            work,
            |root, work| self.constant(root, work),
            |root, work| self.projection(root, work),
        )
    }
    pub(super) fn constant(
        &self,
        root: ExprId,
        work: &mut Working<'_>,
    ) -> Result<Option<ExprId>, Stop> {
        let (name, count) = match work.expressions.get(root, work.budget)?.kind(
            work.expressions,
            work.levels,
            work.budget,
        )? {
            ExprKind::Constant(name, levels) => (name, levels.len()),
            ExprKind::Free(_) => return Err(ResourceError::Invariant.into()),
            _ => return Ok(None),
        };
        let Some(index) = self.find(name, work)? else {
            naming::public_name(name, work)?;
            return Ok(None);
        };
        let family_count = self.queue.families.len();
        let ctor_end = family_count
            .checked_add(self.queue.constructors.len())
            .ok_or(ResourceError::Counter)?;
        if index < ctor_end {
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
        }
        if index < family_count {
            let family = self.queue.families[index];
            return self
                .queue
                .keys
                .get(family.key as usize)
                .map(|key| Some(key.root))
                .ok_or_else(|| ResourceError::Invariant.into());
        }
        if index < ctor_end {
            return self
                .constructor_application(index - family_count, work)
                .map(Some);
        }
        let public = self.recursor(index - ctor_end)?;
        let mut levels = Vec::new();
        let result = (|| {
            work.budget.grow_vec(&mut levels, count)?;
            let ExprKind::Constant(_, original) = work.expressions.get(root, work.budget)?.kind(
                work.expressions,
                work.levels,
                work.budget,
            )?
            else {
                return Err(ResourceError::Invariant.into());
            };
            work.budget.charge_work(original.len() as u64)?;
            levels.extend_from_slice(original);
            application(public, &levels, &[], work).map(Some)
        })();
        release(levels, work.budget)?;
        result
    }
    fn constructor_application(
        &self,
        index: usize,
        work: &mut Working<'_>,
    ) -> Result<ExprId, Stop> {
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
        let mut key = self
            .queue
            .keys
            .get(family.key as usize)
            .ok_or(ResourceError::Invariant)?
            .root;
        let mut args = Vec::new();
        let mut levels = Vec::new();
        let result = (|| {
            loop {
                match work.expressions.get(key, work.budget)?.kind(
                    work.expressions,
                    work.levels,
                    work.budget,
                )? {
                    ExprKind::App(function, argument) => {
                        push(&mut args, argument, work.budget)?;
                        key = function;
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
            application(constructor.prior, &levels, &args, work)
        })();
        release(args, work.budget)?;
        release(levels, work.budget)?;
        result
    }
    pub(super) fn projection(&self, root: ExprId, work: &mut Working<'_>) -> Result<ExprId, Stop> {
        let ExprKind::Projection(name, field, source) = work
            .expressions
            .get(root, work.budget)?
            .kind(work.expressions, work.levels, work.budget)?
        else {
            return Ok(root);
        };
        let Some(index) = self.find(name, work)? else {
            naming::public_name(name, work)?;
            return Ok(root);
        };
        let family = self
            .queue
            .families
            .get(index)
            .ok_or(ResourceError::Invariant)?;
        Ok(work.expressions.append(
            ExprKind::Projection(family.prior, field, source),
            work.levels,
            work.names,
            work.budget,
        )?)
    }
    pub(super) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        release(self.rows, budget)?;
        release(self.public_recursors, budget)
    }
}
fn name_error(error: crate::syntax::names::NameError) -> Stop {
    match error {
        crate::syntax::names::NameError::Resource(error) => error.into(),
        _ => ResourceError::Invariant.into(),
    }
}
fn public_recursor(first: NameId, mut index: u32, work: &mut Working<'_>) -> Result<NameId, Stop> {
    let mut text = [0u8; 14];
    let mut start = text.len();
    loop {
        start -= 1;
        text[start] = b'0' + (index % 10) as u8;
        index /= 10;
        if index == 0 {
            break;
        }
    }
    start -= 4;
    text[start..start + 4].copy_from_slice(b"rec_");
    work.names
        .append(
            first,
            Component::String(
                std::str::from_utf8(&text[start..]).map_err(|_| ResourceError::Invariant)?,
            ),
            work.budget,
        )
        .map_err(name_error)
}

mod parameterized;
