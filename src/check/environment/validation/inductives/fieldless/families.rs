//! Block-local exact canonical-name membership. No expression or equality cache.
//! Rows map a canonical name to its position in the checked specification order.
use super::*;

#[derive(Default)]
pub(super) struct FamilySet {
    rows: Vec<(u32, u32)>,
}
impl FamilySet {
    pub(super) fn fill(
        &mut self,
        work: &mut Working<'_>,
        families: impl ExactSizeIterator<Item = NameId>,
    ) -> Result<(), Stop> {
        if !self.rows.is_empty() {
            return Err(ResourceError::Invariant.into());
        }
        let count = families.len();
        work.budget.charge_work(
            (count as u64)
                .checked_mul(u64::from(count.checked_ilog2().unwrap_or(0)) + 2)
                .ok_or(ResourceError::Counter)?,
        )?;
        work.budget.grow_vec(&mut self.rows, count)?;
        for (index, family) in families.enumerate() {
            let key = work.names.summary(family, work.budget)?.canonical;
            self.rows.push((
                key,
                u32::try_from(index).map_err(|_| ResourceError::Counter)?,
            ));
        }
        self.rows.sort_unstable_by_key(|row| row.0);
        if self.rows.windows(2).any(|rows| rows[0].0 == rows[1].0) {
            return Err(Stop::Judgment(
                crate::decode::primitive_decode::ordinary_session::Negative::TypeMismatch,
            ));
        }
        Ok(())
    }
    pub(super) fn find(
        &self,
        name: NameId,
        names: &Names,
        budget: &mut Budget,
    ) -> Result<Option<usize>, ResourceError> {
        budget.charge_work(u64::from(self.rows.len().checked_ilog2().unwrap_or(0)) + 1)?;
        let key = names.summary(name, budget)?.canonical;
        Ok(self
            .rows
            .binary_search_by_key(&key, |row| row.0)
            .ok()
            .map(|index| self.rows[index].1 as usize))
    }
    pub(super) fn retire(self, budget: &mut Budget) -> Result<(), ResourceError> {
        let bytes = self.rows.capacity() * std::mem::size_of::<(u32, u32)>();
        drop(self);
        budget.release(bytes as u64)
    }
}

pub(super) fn with_set<T>(
    work: &mut Working<'_>,
    families: impl ExactSizeIterator<Item = NameId>,
    f: impl FnOnce(&mut Working<'_>, &FamilySet) -> Result<T, Stop>,
) -> Result<T, Stop> {
    let mut set = FamilySet::default();
    let result = (|| {
        set.fill(work, families)?;
        f(work, &set)
    })();
    set.retire(work.budget)?;
    result
}
