//! Private input view for the shared derivation algorithm. This supplies syntax
//! and ordering, never checkedness, serialized computation rules or authority.
use super::*;

pub(in super::super) struct FamilyInput<'a> {
    pub name: NameId,
    pub ty: ExprId,
    pub num_params: u32,
    pub parameters: &'a [NameId],
    pub constructors: usize,
}
pub(in super::super) struct ConstructorInput {
    pub name: NameId,
    pub ty: ExprId,
}
pub(in super::super) trait Templates {
    fn family_names(&self) -> impl ExactSizeIterator<Item = NameId> + '_;
    fn family_count(&self) -> usize;
    fn family(&self, index: usize) -> Result<FamilyInput<'_>, ResourceError>;
    fn constructor(
        &self,
        member: usize,
        index: usize,
        work: &mut Working<'_>,
    ) -> Result<ConstructorInput, Stop>;
    fn recursor_count(&self) -> usize;
    fn recursor_name(&self, index: usize, work: &mut Working<'_>) -> Result<NameId, Stop>;
}
impl Templates for Request<'_> {
    fn family_names(&self) -> impl ExactSizeIterator<Item = NameId> + '_ {
        self.types.iter().map(|family| family.name)
    }
    fn family_count(&self) -> usize {
        self.types.len()
    }
    fn family(&self, index: usize) -> Result<FamilyInput<'_>, ResourceError> {
        let family = self.types.get(index).ok_or(ResourceError::Invariant)?;
        Ok(FamilyInput {
            name: family.name,
            ty: family.ty,
            num_params: family.num_params,
            parameters: list(self.names, family.parameters)?,
            constructors: list(self.names, family.constructors)?.len(),
        })
    }
    fn constructor(
        &self,
        member: usize,
        index: usize,
        work: &mut Working<'_>,
    ) -> Result<ConstructorInput, Stop> {
        let family = self.types.get(member).ok_or(ResourceError::Invariant)?;
        let &name = list(self.names, family.constructors)?
            .get(index)
            .ok_or(ResourceError::Invariant)?;
        // Preserve the existing original-input lookup and its charge sequence.
        for constructor in self.constructors {
            work.budget.charge_work(1)?;
            if same(work.names, constructor.name, name, work.budget)? {
                return Ok(ConstructorInput {
                    name: constructor.name,
                    ty: constructor.ty,
                });
            }
        }
        Err(ResourceError::Invariant.into())
    }
    fn recursor_count(&self) -> usize {
        self.recursors.len()
    }
    fn recursor_name(&self, index: usize, _work: &mut Working<'_>) -> Result<NameId, Stop> {
        self.recursors
            .get(index)
            .map(|r| r.name)
            .ok_or_else(|| ResourceError::Invariant.into())
    }
}
