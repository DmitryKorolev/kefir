//! Node storage for the expression store.
//!
//! Native builds keep one `Vec`. On wasm32 (4 GiB address space, at most 2 GiB per
//! allocation, memory never returned) one contiguous node vector cannot hold
//! Mathlib, and regrowing it needs the old and new buffers at once. Wasm builds
//! therefore keep fixed chunks of `CHUNK` nodes, allocated only when the last one
//! is full, so growth never copies. Budget charges follow the native vector's
//! logical capacity (same doubling, copy charge, reserve and release), so both
//! builds charge identically for this store.
use super::StoredExpression;
use crate::resource::{Budget, ResourceError};

#[cfg(not(target_family = "wasm"))]
pub(super) type Nodes = Vec<StoredExpression>;

/// Whether `required` nodes fit without growing.
#[cfg(not(target_family = "wasm"))]
#[inline(always)]
pub(super) fn has_room(nodes: &Nodes, required: usize) -> bool {
    required <= nodes.capacity()
}

#[cfg(not(target_family = "wasm"))]
#[inline(always)]
pub(super) fn grow(
    budget: &mut Budget,
    nodes: &mut Nodes,
    required: usize,
) -> Result<(), ResourceError> {
    budget.grow_vec(nodes, required)
}

#[cfg(target_family = "wasm")]
pub(super) use chunked::{Nodes, grow, has_room};

#[cfg(target_family = "wasm")]
mod chunked {
    use super::{Budget, ResourceError, StoredExpression};

    const SHIFT: u32 = 20;
    const CHUNK: usize = 1 << SHIFT;
    const MASK: usize = CHUNK - 1;

    /// Nodes in fixed chunks. `logical` is the capacity a native `Vec` would have
    /// after the same growth requests; only it is charged.
    #[derive(Default)]
    pub(in crate::syntax::expressions) struct Nodes {
        chunks: Vec<Vec<StoredExpression>>,
        len: usize,
        logical: usize,
    }

    impl Nodes {
        #[inline(always)]
        pub(in crate::syntax::expressions) fn len(&self) -> usize {
            self.len
        }
        /// The native-equivalent logical capacity (accounting only).
        #[allow(dead_code)]
        pub(in crate::syntax::expressions) fn capacity(&self) -> usize {
            self.logical
        }
        fn physical(&self) -> usize {
            self.chunks.len() * CHUNK
        }
        #[inline(always)]
        pub(in crate::syntax::expressions) fn get(
            &self,
            index: usize,
        ) -> Option<&StoredExpression> {
            if index >= self.len {
                return None;
            }
            self.chunks.get(index >> SHIFT)?.get(index & MASK)
        }
        #[inline(always)]
        pub(in crate::syntax::expressions) fn push(&mut self, node: StoredExpression) {
            // has_room/grow allocated the chunk holding index `len` before any
            // push; a batch reservation may have allocated later chunks too.
            let chunk = &mut self.chunks[self.len >> SHIFT];
            debug_assert_eq!(chunk.len(), self.len & MASK);
            chunk.push(node);
            self.len += 1;
        }
        pub(in crate::syntax::expressions) fn truncate(&mut self, len: usize) {
            if len >= self.len {
                return;
            }
            let keep = len.div_ceil(CHUNK).max(1).min(self.chunks.len());
            self.chunks.truncate(keep);
            if let Some(last) = self.chunks.last_mut() {
                last.truncate(len - (keep - 1) * CHUNK);
            }
            self.len = len;
        }
        #[allow(dead_code)]
        pub(in crate::syntax::expressions) fn iter(
            &self,
        ) -> impl Iterator<Item = &StoredExpression> {
            self.chunks.iter().flatten()
        }
    }

    impl std::ops::Index<usize> for Nodes {
        type Output = StoredExpression;
        #[inline(always)]
        fn index(&self, index: usize) -> &StoredExpression {
            self.get(index).expect("node index in range")
        }
    }

    impl std::ops::IndexMut<usize> for Nodes {
        #[inline(always)]
        fn index_mut(&mut self, index: usize) -> &mut StoredExpression {
            assert!(index < self.len, "node index in range");
            &mut self.chunks[index >> SHIFT][index & MASK]
        }
    }

    /// Whether `required` nodes fit without growing: within the native vector's
    /// logical capacity, so `grow` charges exactly when native growth would, and
    /// within the chunks already allocated.
    #[inline(always)]
    pub(in crate::syntax::expressions) fn has_room(nodes: &Nodes, required: usize) -> bool {
        required <= nodes.logical && required <= nodes.physical()
    }

    /// Charge exactly as `Budget::grow_vec` would for a native vector of logical
    /// capacity `nodes.logical`, then allocate whole chunks to cover `required`.
    pub(in crate::syntax::expressions) fn grow(
        budget: &mut Budget,
        nodes: &mut Nodes,
        required: usize,
    ) -> Result<(), ResourceError> {
        if required <= nodes.logical {
            return allocate(nodes, required);
        }
        // Same order and arithmetic as `Budget::grow_vec`: charge the copy, reserve
        // the new logical bytes, allocate, and on failure release the new bytes and
        // keep the old logical capacity. Byte counts are u64 so a 32-bit usize
        // never turns a native charge into a counter overflow.
        let old = nodes.logical;
        let capacity = old
            .checked_mul(2)
            .ok_or(ResourceError::Counter)?
            .max(required)
            .max(8);
        let item = crate::resource::charged::bytes::<StoredExpression>() as u64;
        let new_bytes = (capacity as u64)
            .checked_mul(item)
            .ok_or(ResourceError::Counter)?;
        let old_bytes = (old as u64)
            .checked_mul(item)
            .ok_or(ResourceError::Counter)?;
        budget.charge_work(old_bytes.checked_add(1).ok_or(ResourceError::Counter)?)?;
        budget.reserve(new_bytes)?;
        if let Err(error) = allocate(nodes, required) {
            budget.release(new_bytes)?;
            return Err(error);
        }
        budget.observe(crate::resource::Event::Allocations, 1);
        nodes.logical = capacity;
        budget.release(old_bytes)
    }

    /// Allocate whole chunks until `required` nodes fit; nothing is charged here.
    fn allocate(nodes: &mut Nodes, required: usize) -> Result<(), ResourceError> {
        while nodes.physical() < required {
            let mut chunk = Vec::new();
            chunk
                .try_reserve_exact(CHUNK)
                .map_err(|_| ResourceError::Allocation)?;
            nodes
                .chunks
                .try_reserve(1)
                .map_err(|_| ResourceError::Allocation)?;
            nodes.chunks.push(chunk);
        }
        Ok(())
    }
}
