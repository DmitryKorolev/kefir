//! Persistent session-local de Bruijn environments, with 32-way path copying.
//! Origin invariant: handles are used only with their creating caller session.
//! Binding slots are opaque caller-owned values, not reusable local identities.
//! No handle interning or cross-store equivalence is supplied here.
use crate::resource::{Budget, ResourceError};
use std::{cell::Cell, mem::size_of};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash)]
pub(crate) struct EnvId(u32);
impl EnvId {
    pub(crate) const EMPTY: Self = Self(0);

    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_slot(self) -> u32 {
        self.0
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct BindingId(u32);
impl BindingId {
    pub(crate) fn new(slot: u32) -> Self {
        Self(slot)
    }
    pub(crate) fn slot(self) -> u32 {
        self.0
    }
}
const MISSING: u32 = u32::MAX;
const LEVELS: usize = 7;
#[derive(Clone, Copy)]
struct Root {
    node: u32,
    len: u32,
    height: u8,
}
#[derive(Clone, Copy)]
struct Block([u32; 32]);
#[derive(Default)]
pub(crate) struct Environment {
    roots: Vec<Root>,
    blocks: Vec<Block>,
    failure: Cell<Option<ResourceError>>,
}
const _: () = assert!(size_of::<EnvId>() == 4);
const _: () = assert!(size_of::<BindingId>() == 4);
const _: () = assert!(size_of::<Root>() == 12);
const _: () = assert!(size_of::<Block>() == 128);
const _: () = assert!(size_of::<Environment>() <= 56);

impl Environment {
    /// Optional read-only diagnostics bypass semantic fuel and sticky operation
    /// state. Handles still require this exact session-owned environment.
    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_len(&self, env: EnvId) -> Result<u32, ResourceError> {
        self.root(env).map(|root| root.len)
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_lookup(
        &self,
        env: EnvId,
        index: u32,
    ) -> Result<BindingId, ResourceError> {
        let root = self.root(env)?;
        let position = root
            .len
            .checked_sub(index)
            .and_then(|n| n.checked_sub(1))
            .ok_or(ResourceError::Invariant)?;
        if usize::from(root.height) >= LEVELS {
            return Err(ResourceError::Invariant);
        }
        let mut node = root.node;
        for level in (0..=root.height).rev() {
            let block = self
                .blocks
                .get(node as usize)
                .ok_or(ResourceError::Invariant)?;
            let digit = ((position >> (u32::from(level) * 5)) & 31) as usize;
            let value = block.0[digit];
            if level == 0 {
                return Ok(BindingId(value));
            }
            node = value;
        }
        Err(ResourceError::Invariant)
    }

    pub(crate) fn new() -> Self {
        Self::default()
    }
    fn begin(&self) -> Result<(), ResourceError> {
        if let Some(error) = self.failure.get() {
            return Err(error);
        }
        // Any unwind leaves the owner unusable, even when its caller catches it.
        self.failure.set(Some(ResourceError::Invariant));
        Ok(())
    }
    fn end<T>(&self, result: Result<T, ResourceError>) -> Result<T, ResourceError> {
        self.failure.set(result.as_ref().err().copied());
        result
    }
    fn root(&self, env: EnvId) -> Result<Root, ResourceError> {
        if env == EnvId::EMPTY {
            return Ok(Root {
                node: MISSING,
                len: 0,
                height: 0,
            });
        }
        self.roots
            .get((env.0 - 1) as usize)
            .copied()
            .ok_or(ResourceError::Invariant)
    }
    pub(crate) fn len(&self, env: EnvId) -> Result<u32, ResourceError> {
        self.begin()?;
        self.end(self.root(env).map(|root| root.len))
    }
    pub(crate) fn lookup(
        &self,
        env: EnvId,
        index: u32,
        b: &mut Budget,
    ) -> Result<BindingId, ResourceError> {
        self.begin()?;
        let result = (|| {
            let root = self.root(env)?;
            let position = root
                .len
                .checked_sub(index)
                .and_then(|n| n.checked_sub(1))
                .ok_or(ResourceError::Invariant)?;
            if usize::from(root.height) >= LEVELS {
                return Err(ResourceError::Invariant);
            }
            b.charge_work(u64::from(root.height) + 2)?;
            let mut node = root.node;
            for level in (0..=root.height).rev() {
                let block = self
                    .blocks
                    .get(node as usize)
                    .ok_or(ResourceError::Invariant)?;
                let digit = ((position >> (u32::from(level) * 5)) & 31) as usize;
                let value = block.0[digit];
                if level == 0 {
                    return Ok(BindingId(value));
                }
                node = value;
            }
            Err(ResourceError::Invariant)
        })();
        self.end(result)
    }
    pub(crate) fn extend(
        &mut self,
        env: EnvId,
        binding: BindingId,
        b: &mut Budget,
    ) -> Result<EnvId, ResourceError> {
        self.begin()?;
        let mark = self.blocks.len();
        let result = self.extend_inner(env, binding, b);
        if result.is_err() {
            self.blocks.truncate(mark);
        }
        self.end(result)
    }
    fn extend_inner(
        &mut self,
        env: EnvId,
        binding: BindingId,
        b: &mut Budget,
    ) -> Result<EnvId, ResourceError> {
        let old = self.root(env)?;
        let len = old.len.checked_add(1).ok_or(ResourceError::Counter)?;
        if usize::from(old.height) >= LEVELS {
            return Err(ResourceError::Invariant);
        }
        let grows = u64::from(old.len) == 1u64 << (5 * (u32::from(old.height) + 1));
        let height = old.height + u8::from(grows);
        let count = usize::from(height) + 1;
        if count > LEVELS {
            return Err(ResourceError::Invariant);
        }
        let next_roots = self
            .roots
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        let id = EnvId(u32::try_from(next_roots).map_err(|_| ResourceError::Counter)?);
        let next_blocks = self
            .blocks
            .len()
            .checked_add(count)
            .ok_or(ResourceError::Counter)?;
        if next_blocks > MISSING as usize {
            return Err(ResourceError::Counter);
        }
        // Charge one bounded traversal plus all 32 entries copied/initialized per
        // block. grow_vec additionally charges old-capacity copying and reserves
        // old+new allocation overlap. No per-entry accounting in the loops.
        b.charge_work(1 + 34 * count as u64)?;
        b.grow_vec(&mut self.roots, next_roots)?;
        b.grow_vec(&mut self.blocks, next_blocks)?;
        b.reserve_frames(count)?;
        let built = self.copy_path(old, binding, height, grows);
        let cleanup = b.release_frames(count);
        // Cleanup defects are internal and take precedence over a failed route.
        cleanup?;
        let node = built?;
        // All capacities and cleanup succeeded: publish exactly one new root.
        self.roots.push(Root { node, len, height });
        Ok(id)
    }
    fn copy_path(
        &mut self,
        old: Root,
        binding: BindingId,
        height: u8,
        grows: bool,
    ) -> Result<u32, ResourceError> {
        let mut path = [MISSING; LEVELS];
        let mut node = if grows { MISSING } else { old.node };
        for level in (0..=height).rev() {
            path[usize::from(level)] = node;
            if node != MISSING {
                let block = self
                    .blocks
                    .get(node as usize)
                    .ok_or(ResourceError::Invariant)?;
                if level != 0 {
                    let digit = ((old.len >> (u32::from(level) * 5)) & 31) as usize;
                    node = block.0[digit];
                }
            }
        }
        let mut child = binding.0;
        for level in 0..=height {
            let original = path[usize::from(level)];
            let mut block = if original == MISSING {
                Block([MISSING; 32])
            } else {
                *self
                    .blocks
                    .get(original as usize)
                    .ok_or(ResourceError::Invariant)?
            };
            if grows && level == height {
                block.0[0] = old.node;
            }
            let digit = ((old.len >> (u32::from(level) * 5)) & 31) as usize;
            block.0[digit] = child;
            child = u32::try_from(self.blocks.len()).map_err(|_| ResourceError::Counter)?;
            self.blocks.push(block);
        }
        Ok(child)
    }
    pub(crate) fn retire(self, b: &mut Budget) -> Result<(), ResourceError> {
        let failure = self.failure.get();
        let bytes =
            self.roots.capacity() * size_of::<Root>() + self.blocks.capacity() * size_of::<Block>();
        drop(self);
        b.release(bytes as u64)?;
        failure.map_or(Ok(()), Err)
    }
}
