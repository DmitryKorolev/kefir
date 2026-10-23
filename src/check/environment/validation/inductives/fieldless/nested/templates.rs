//! Membership-derived ordering, not a decoded declaration or admission certificate.
//! This owner borrows originals; its dense indices survive only this nested request.
use super::*;

#[derive(Default)]
pub(super) struct Order {
    pub(super) families: Vec<u32>,
    pub(super) constructors: Vec<u32>,
}
const _: () = assert!(size_of::<Order>() == 48);
impl Order {
    pub(super) fn build(
        &mut self,
        request: &Request<'_>,
        work: &mut Working<'_>,
    ) -> Result<(), Stop> {
        let first = request.types.first().ok_or(Stop::Unsupported)?;
        let members = list(request.names, first.all)?;
        let parameters = list(request.names, first.parameters)?;
        if members.len() != request.types.len() || members.is_empty() {
            return Err(Stop::Unsupported);
        }
        for &member in members {
            let mut found = None;
            for (index, family) in request.types.iter().enumerate() {
                if same(work.names, member, family.name, work.budget)?
                    && found.replace(index).is_some()
                {
                    return Err(Stop::Unsupported);
                }
            }
            let index = found.ok_or(Stop::Unsupported)?;
            let encoded = u32::try_from(index).map_err(|_| ResourceError::Counter)?;
            work.budget.charge_work(self.families.len() as u64)?;
            if self.families.contains(&encoded) {
                return Err(Stop::Unsupported);
            }
            let family = &request.types[index];
            if family.num_params != first.num_params
                || !parameters_equal(
                    work.names,
                    parameters,
                    list(request.names, family.parameters)?,
                    work.budget,
                )?
                || !parameters_equal(
                    work.names,
                    members,
                    list(request.names, family.all)?,
                    work.budget,
                )?
            {
                return Err(Stop::Unsupported);
            }
            push(&mut self.families, encoded, work.budget)?;
            for (ordinal, &name) in list(request.names, family.constructors)?.iter().enumerate() {
                let mut found = None;
                for (index, ctor) in request.constructors.iter().enumerate() {
                    if same(work.names, name, ctor.name, work.budget)?
                        && found.replace(index).is_some()
                    {
                        return Err(Stop::Unsupported);
                    }
                }
                let index = found.ok_or(Stop::Unsupported)?;
                let encoded = u32::try_from(index).map_err(|_| ResourceError::Counter)?;
                work.budget.charge_work(self.constructors.len() as u64)?;
                if self.constructors.contains(&encoded) {
                    return Err(Stop::Unsupported);
                }
                let ctor = &request.constructors[index];
                if ctor.index as usize != ordinal
                    || ctor.num_params != first.num_params
                    || !same(work.names, ctor.inductive, member, work.budget)?
                    || !parameters_equal(
                        work.names,
                        parameters,
                        list(request.names, ctor.parameters)?,
                        work.budget,
                    )?
                {
                    return Err(Stop::Unsupported);
                }
                push(&mut self.constructors, encoded, work.budget)?;
            }
        }
        if self.constructors.len() != request.constructors.len() {
            return Err(Stop::Unsupported);
        }
        Ok(())
    }
    pub(super) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        let a = release(self.families, budget);
        let b = release(self.constructors, budget);
        a?;
        b
    }
}
fn push(v: &mut Vec<u32>, value: u32, budget: &mut Budget) -> Result<(), Stop> {
    budget.grow_vec(v, v.len().checked_add(1).ok_or(ResourceError::Counter)?)?;
    v.push(value);
    Ok(())
}
fn release(v: Vec<u32>, budget: &mut Budget) -> Result<(), ResourceError> {
    let bytes = v.capacity().checked_mul(4).ok_or(ResourceError::Counter)?;
    drop(v);
    budget.release(bytes as u64)
}
