//! Borrowed, ordered syntax for shared family/constructor derivation. This is not
//! a decoded Request: it has no serialized flags, recursor rules or authority.
use super::super::super::scheme::{ConstructorInput, FamilyInput, Templates};
use super::*;

pub(super) struct Expanded<'a, 'r> {
    queue: &'a Queue,
    request: &'a Request<'r>,
    order: &'a Order,
    parameters: &'a [NameId],
    count: usize,
}
impl<'a, 'r> Expanded<'a, 'r> {
    pub(super) fn new(
        queue: &'a Queue,
        request: &'a Request<'r>,
        order: &'a Order,
    ) -> Result<Self, Stop> {
        if order.families.len() != request.types.len()
            || order.constructors.len() != queue.original_constructors.len()
        {
            return Err(ResourceError::Invariant.into());
        }
        let parameters = list(
            request.names,
            request
                .types
                .first()
                .ok_or(ResourceError::Invariant)?
                .parameters,
        )?;
        let count = order
            .families
            .len()
            .checked_add(queue.families.len())
            .ok_or(ResourceError::Counter)?;
        Ok(Self {
            queue,
            request,
            order,
            parameters,
            count,
        })
    }
    fn name(&self, index: usize) -> NameId {
        // Order is built from exact, complete membership before queue discovery;
        // the private range iterator below cannot exceed those validated spans.
        if index < self.order.families.len() {
            self.request.types[self.order.families[index] as usize].name
        } else {
            self.queue.families[index - self.order.families.len()].helper
        }
    }
    pub(super) fn raw(&self, work: &mut Working<'_>) -> Result<bool, Stop> {
        families::with_set(work, self.family_names(), |work, members| {
            for member in 0..self.count {
                let family = self.family(member)?;
                for index in 0..family.constructors {
                    let constructor = self.constructor(member, index, work)?;
                    if !raw_constructor_template(
                        work,
                        self.raw_family(member)?,
                        members,
                        self,
                        self.parameters,
                        constructor.ty,
                    )? {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        })
    }
}
impl RawFamilies for Expanded<'_, '_> {
    fn raw_family(&self, index: usize) -> Result<RawFamily, ResourceError> {
        let family = self.family(index)?;
        Ok(RawFamily {
            name: family.name,
            num_params: family.num_params,
        })
    }
}
impl Templates for Expanded<'_, '_> {
    fn family_names(&self) -> impl ExactSizeIterator<Item = NameId> + '_ {
        (0..self.count).map(|index| self.name(index))
    }
    fn family_count(&self) -> usize {
        self.count
    }
    fn family(&self, index: usize) -> Result<FamilyInput<'_>, ResourceError> {
        if let Some(&original) = self.order.families.get(index) {
            let family = &self.request.types[original as usize];
            Ok(FamilyInput {
                name: family.name,
                ty: family.ty,
                num_params: family.num_params,
                parameters: self.parameters,
                constructors: list(self.request.names, family.constructors)?.len(),
            })
        } else {
            let family = self
                .queue
                .families
                .get(
                    index
                        .checked_sub(self.order.families.len())
                        .ok_or(ResourceError::Invariant)?,
                )
                .ok_or(ResourceError::Invariant)?;
            Ok(FamilyInput {
                name: family.helper,
                ty: family.ty,
                num_params: self.request.types[*self
                    .order
                    .families
                    .first()
                    .ok_or(ResourceError::Invariant)?
                    as usize]
                    .num_params,
                parameters: self.parameters,
                constructors: family.count as usize,
            })
        }
    }
    fn constructor(
        &self,
        member: usize,
        index: usize,
        work: &mut Working<'_>,
    ) -> Result<ConstructorInput, Stop> {
        let family = self.family(member)?;
        if index >= family.constructors {
            return Err(ResourceError::Invariant.into());
        }
        if member < self.order.families.len() {
            let mut offset = 0usize;
            work.budget.charge_work(member as u64 + 1)?;
            for previous in 0..member {
                offset = offset
                    .checked_add(self.family(previous)?.constructors)
                    .ok_or(ResourceError::Counter)?;
            }
            offset = offset.checked_add(index).ok_or(ResourceError::Counter)?;
            let original = *self
                .order
                .constructors
                .get(offset)
                .ok_or(ResourceError::Invariant)? as usize;
            Ok(ConstructorInput {
                name: self.request.constructors[original].name,
                ty: *self
                    .queue
                    .original_constructors
                    .get(offset)
                    .ok_or(ResourceError::Invariant)?,
            })
        } else {
            let family = &self.queue.families[member - self.order.families.len()];
            let offset = (family.constructors as usize)
                .checked_add(index)
                .ok_or(ResourceError::Counter)?;
            let constructor = self
                .queue
                .constructors
                .get(offset)
                .ok_or(ResourceError::Invariant)?;
            Ok(ConstructorInput {
                name: constructor.helper,
                ty: constructor.ty,
            })
        }
    }
    // This bounded preparation derives positivity only. Recursor names and
    // types must be generated/rechecked by the subsequent owned-template slice;
    // imported recursor rows cannot stand in for expanded computation authority.
    fn recursor_count(&self) -> usize {
        0
    }
    fn recursor_name(&self, _: usize, _: &mut Working<'_>) -> Result<NameId, Stop> {
        Err(ResourceError::Invariant.into())
    }
}
