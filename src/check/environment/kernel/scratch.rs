//! Kernel-owned temporary buffers, empty between uses. May retain the
//! pool with its graph in one State; no live cursor or borrowed view survives.
//! The logical capacity is charged while active, pooled or retained.
//! Only `Kernel::scratch_room` may grow it; mutable
//! vector access is for writes after admission, and non-growing operations.
use std::ops::{Deref, DerefMut};

#[derive(Default)]
pub(super) struct Scratch {
    pub(super) values: Vec<u32>,
    pub(super) slots: usize,
}
const _: () = assert!(std::mem::size_of::<Scratch>() == 32);

impl Deref for Scratch {
    type Target = Vec<u32>;
    fn deref(&self) -> &Self::Target {
        &self.values
    }
}
impl DerefMut for Scratch {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}
impl<'a> IntoIterator for &'a Scratch {
    type Item = &'a u32;
    type IntoIter = std::slice::Iter<'a, u32>;
    fn into_iter(self) -> Self::IntoIter {
        self.values.iter()
    }
}
impl<'a> IntoIterator for &'a mut Scratch {
    type Item = &'a mut u32;
    type IntoIter = std::slice::IterMut<'a, u32>;
    fn into_iter(self) -> Self::IntoIter {
        self.values.iter_mut()
    }
}
