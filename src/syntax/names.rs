//! Structured names: raw handles, exact canonical ids and flat payloads.
//! Canonical identity is name equality only, never declaration installation or
//! level-scope authority. Every handle and ledger belongs to one originating run.
use crate::resource::{Budget, ResourceError, STRUCTURE_DEPTH};
use crate::syntax::levels::{LevelNames, NameId, NameSummary, OrderedLevelNames};
use std::cmp::Ordering;
use std::hash::Hasher;
use std::mem::size_of;

#[cfg(feature = "introspection")]
pub(crate) mod diagnostic;

impl NameId {
    pub(crate) const ANONYMOUS: Self = Self(0);
}

#[derive(Clone, Copy)]
pub(crate) enum Component<'a> {
    Number(&'a [u8]),
    String(&'a str),
}

#[cfg(feature = "introspection")]
#[derive(Clone, Copy)]
pub(crate) enum DiagnosticComponent<'a> {
    Number(&'a [u8]),
    String(&'a [u8]),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NameError {
    Resource(ResourceError),
    InvalidNumber,
    NumericRange,
}
impl From<ResourceError> for NameError {
    fn from(e: ResourceError) -> Self {
        Self::Resource(e)
    }
}

#[derive(Clone, Copy, Default)]
struct Name {
    tag: u32, // 0 anonymous, 1 number, 2 string; this is also component order.
    prefix: u32,
    canonical: u32,
    offset: u32,
    len: u32,
    depth: u32,
}
const _: () = assert!(size_of::<Name>() == 24);

#[derive(Clone, Copy, Default)]
struct Entry {
    hash: u64,
    name: u32,
}
const _: () = assert!(size_of::<Entry>() == 16);

/// Raw nodes remain distinct; the canonical table references the first raw
/// representative of each exact structured name. That representative's slot is
/// its canonical id. Append preserves all existing nodes; discard_since removes
/// only a generated suffix with no surviving references. Retained-root compaction
/// still requires remapping this table separately.
/// These flat stores own their charged capacities until the run ledger is
/// retired; dropping Names is not permission to reuse that ledger's live count.
pub(crate) struct Names {
    nodes: Vec<Name>,
    bytes: Vec<u8>,
    entries: Vec<Entry>,
    unique: usize,
}

impl Names {
    /// Optional diagnostics read exact validated components without semantic
    /// lookup events or work charges. The returned bytes borrow this table.
    #[cfg(feature = "introspection")]
    pub(crate) fn diagnostic_component(
        &self,
        id: NameId,
    ) -> Result<Option<(NameId, DiagnosticComponent<'_>)>, ResourceError> {
        let name = self.get(id)?;
        Ok(match name.tag {
            0 if id == NameId::ANONYMOUS => None,
            1 => Some((
                NameId(name.prefix),
                DiagnosticComponent::Number(self.payload(name)),
            )),
            // String components were validated before installation. Diagnostics
            // decode only the bounded prefix that they can emit, rather than
            // rescanning an input-sized component here.
            2 => Some((
                NameId(name.prefix),
                DiagnosticComponent::String(self.payload(name)),
            )),
            _ => return Err(ResourceError::Invariant),
        })
    }

    pub(crate) fn prefix(
        &self,
        id: NameId,
        b: &mut Budget,
    ) -> Result<Option<NameId>, ResourceError> {
        b.observe(crate::resource::Event::TableLookups, 1);
        let n = self.get(id)?;
        Ok((n.tag != 0).then_some(NameId(n.prefix)))
    }
    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Read the existing canonical component index without creating a raw name.
    /// This supplies name identity only; callers must still check declaration
    /// visibility and authority. Component bytes obey the append contract.
    pub(crate) fn find_component(
        &self,
        prefix: NameId,
        component: Component<'_>,
        b: &mut Budget,
    ) -> Result<Option<NameId>, ResourceError> {
        let (tag, bytes) = match component {
            Component::Number(n) => (1, n),
            Component::String(s) => (2, s.as_bytes()),
        };
        b.charge_work(bytes.len() as u64 + 1)?;
        let prefix = self.get(prefix)?.canonical;
        if self.entries.is_empty() {
            return Ok(None);
        }
        let hash = Self::hash(prefix, tag, bytes);
        let slot = self.position(hash, prefix, tag, bytes, b)?;
        let entry = self.entries[slot];
        Ok((entry.hash != 0).then_some(NameId(entry.name)))
    }

    /// Discard a generated suffix with NO retained generated roots.
    /// `end` is this store's length at declaration entry, never a foreign/stale
    /// frontier. Before calling, the owner must retire every generated reference
    /// in expressions, levels, locals, frames, caches and environment candidates.
    /// Decoded ID maps refer only below `end`. Slot reuse is sound only under
    /// these construction invariants; this method grants no semantic judgment.
    ///
    /// On exhaustion some suffix may already be gone, but remaining nodes/index
    /// stay consistent. The caller must terminate/discard the run, not publish a
    /// declaration or resume checking. Capacities remain owned and charged for
    /// reuse. No full retained-node-prefix scan, extra allocation or tombstone.
    /// Probe clusters may contain retained entries; adversarial clusters can
    /// cause quadratic total work, with every visit charged.
    pub(crate) fn discard_since(
        &mut self,
        end: usize,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        b.charge_work(1)?;
        if end == 0 || end > self.nodes.len() {
            return Err(ResourceError::Invariant);
        }
        while self.nodes.len() > end {
            b.charge_work(1)?;
            let id = self.nodes.len() - 1;
            let n = self.nodes[id];
            if n.canonical as usize == id {
                // Descending removal has already discarded every duplicate and
                // descendant of this first representative. Its prefix survives.
                let prefix = self.get(NameId(n.prefix))?.canonical;
                b.charge_work(n.len as u64 + 1)?;
                let hash = Self::hash(prefix, n.tag, self.payload(n));
                let slot = self.position(hash, prefix, n.tag, self.payload(n), b)?;
                if self.entries[slot].name as usize != id || self.unique == 0 {
                    return Err(ResourceError::Invariant);
                }
                self.remove_entry(slot, b)?;
                self.unique -= 1;
            }
            self.bytes.truncate(n.offset as usize);
            self.nodes.pop();
        }
        Ok(())
    }

    fn remove_entry(&mut self, slot: usize, b: &mut Budget) -> Result<(), ResourceError> {
        let mask = self.entries.len() - 1;
        let mut stop = (slot + 1) & mask;
        // Reserve both the discovery and mutation pass before touching a bucket.
        // A failed reservation leaves the index intact. Load <= 3/4 guarantees
        // a terminating vacancy; explicit bound handles an invariant violation.
        let mut vacant = false;
        for _ in 0..self.entries.len() {
            b.charge_work(2)?;
            if self.entries[stop].hash == 0 {
                vacant = true;
                break;
            }
            stop = (stop + 1) & mask;
        }
        if !vacant {
            return Err(ResourceError::Invariant);
        }
        let mut hole = slot;
        let mut next = (slot + 1) & mask;
        while next != stop {
            let entry = self.entries[next];
            let home = entry.hash as usize & mask;
            // Move only when the vacant bucket lies on this entry's cyclic
            // probe path. Moving across its home would make lookup lose it.
            if hole.wrapping_sub(home) & mask < next.wrapping_sub(home) & mask {
                self.entries[hole] = entry;
                hole = next;
            }
            next = (next + 1) & mask;
        }
        self.entries[hole] = Entry::default();
        Ok(())
    }
    /// Exact raw prefix/component view; anonymous is the sole absent component.
    pub(crate) fn view(
        &self,
        id: NameId,
        b: &mut Budget,
    ) -> Result<Option<(NameId, Component<'_>)>, ResourceError> {
        // Count API attempts, including invalid handles and work denial.
        b.observe(crate::resource::Event::TableLookups, 1);
        let n = self.get(id)?;
        b.charge_work(n.len as u64 + 1)?;
        Ok(match n.tag {
            0 => None,
            1 => Some((NameId(n.prefix), Component::Number(self.payload(n)))),
            2 => Some((
                NameId(n.prefix),
                Component::String(
                    std::str::from_utf8(self.payload(n)).map_err(|_| ResourceError::Invariant)?,
                ),
            )),
            _ => return Err(ResourceError::Invariant),
        })
    }
    pub(crate) fn new(b: &mut Budget) -> Result<Self, ResourceError> {
        b.charge_work(1)?;
        let mut nodes = Vec::new();
        b.grow_vec(&mut nodes, 1)?;
        nodes.push(Name::default());
        Ok(Self {
            nodes,
            bytes: Vec::new(),
            entries: Vec::new(),
            unique: 0,
        })
    }

    fn get(&self, id: NameId) -> Result<Name, ResourceError> {
        self.nodes
            .get(id.0 as usize)
            .copied()
            .ok_or(ResourceError::Invariant)
    }

    pub(crate) fn resolve_slot(&self, slot: u32, b: &mut Budget) -> Result<NameId, ResourceError> {
        b.observe(crate::resource::Event::TableLookups, 1);
        self.get(NameId(slot))?;
        Ok(NameId(slot))
    }

    fn payload(&self, n: Name) -> &[u8] {
        // Construction checks this span before append. Storage is append-only;
        // a name never references record-buffer memory or an uncommitted prefix.
        &self.bytes[n.offset as usize..n.offset as usize + n.len as usize]
    }

    fn hash(prefix: u32, tag: u32, bytes: &[u8]) -> u64 {
        let mut h = crate::syntax::hash::FastHasher::new();
        h.write_u32(prefix);
        h.write_u32(tag);
        h.write(bytes);
        let hash = h.finish();
        if hash == 0 { 1 } else { hash }
    }

    fn position(
        &self,
        hash: u64,
        prefix: u32,
        tag: u32,
        bytes: &[u8],
        b: &mut Budget,
    ) -> Result<usize, ResourceError> {
        let mask = self
            .entries
            .len()
            .checked_sub(1)
            .ok_or(ResourceError::Invariant)?;
        let mut slot = hash as usize & mask;
        for _ in 0..self.entries.len() {
            b.charge_work(1)?;
            let entry = self.entries[slot];
            if entry.hash == 0 {
                return Ok(slot);
            }
            if entry.hash == hash {
                let n = self.get(NameId(entry.name))?;
                let p = self.get(NameId(n.prefix))?;
                if p.canonical == prefix && n.tag == tag && n.len as usize == bytes.len() {
                    b.charge_work(bytes.len() as u64 + 1)?;
                    if self.payload(n) == bytes {
                        return Ok(slot);
                    }
                }
            }
            slot = (slot + 1) & mask;
        }
        Err(ResourceError::Invariant)
    }

    fn grow_index(&mut self, b: &mut Budget) -> Result<(), ResourceError> {
        let capacity = self
            .entries
            .len()
            .checked_mul(2)
            .ok_or(ResourceError::Counter)?
            .max(16);
        let mut replacement = Vec::new();
        b.grow_vec(&mut replacement, capacity)?;
        let result = (|| {
            b.charge_work(capacity as u64 + 1)?;
            replacement.resize(capacity, Entry::default());
            let mask = capacity - 1;
            for e in self.entries.iter().copied().filter(|e| e.hash != 0) {
                let mut slot = e.hash as usize & mask;
                let mut placed = false;
                for _ in 0..capacity {
                    b.charge_work(1)?;
                    if replacement[slot].hash == 0 {
                        replacement[slot] = e;
                        placed = true;
                        break;
                    }
                    slot = (slot + 1) & mask;
                }
                if !placed {
                    return Err(ResourceError::Invariant);
                }
            }
            Ok(())
        })();
        if let Err(e) = result {
            release(replacement, b)?;
            return Err(e);
        }
        let old = std::mem::replace(&mut self.entries, replacement);
        release(old, b)
    }

    /// Component bytes are decoded UTF-8 or canonical decimal digits, not JSON.
    /// Scanner integration must supply exactly the decoded real-format payload.
    /// All calls use this run's unchanged name table and original charged ledger.
    /// Failure publishes no raw node or canonical entry; reserved capacity may
    /// remain owned. The caller publishes the serialized id only after success.
    pub(crate) fn append(
        &mut self,
        prefix: NameId,
        component: Component<'_>,
        b: &mut Budget,
    ) -> Result<NameId, NameError> {
        let (tag, bytes) = match component {
            Component::Number(n) => (1, n),
            Component::String(s) => (2, s.as_bytes()),
        };
        // One span reservation covers validation, hashing and payload copying.
        // It is never charged once per byte inside any of those loops.
        b.charge_work(bytes.len() as u64 + 1)?;
        if tag == 1
            && (bytes.is_empty()
                || (bytes.len() > 1 && bytes[0] == b'0')
                || !bytes.iter().all(u8::is_ascii_digit))
        {
            return Err(NameError::InvalidNumber);
        }
        let p = self.get(prefix)?;
        let depth = p.depth.checked_add(1).ok_or(ResourceError::Counter)?;
        if crate::resource::traced!("names.limit", (depth, STRUCTURE_DEPTH), {
            depth > STRUCTURE_DEPTH
        }) {
            return Err(ResourceError::StructureDepth.into());
        }
        let len = u32::try_from(bytes.len()).map_err(|_| NameError::NumericRange)?;
        let end = self
            .bytes
            .len()
            .checked_add(bytes.len())
            .ok_or(ResourceError::Counter)?;
        crate::resource::traced!("names.slot_limit", end, {
            u32::try_from(end).map_err(|_| ResourceError::Storage)
        })?;
        let slot = crate::resource::traced!("names.slot_limit", self.nodes.len(), {
            u32::try_from(self.nodes.len()).map_err(|_| ResourceError::Storage)
        })?;
        let hash = Self::hash(p.canonical, tag, bytes);
        let mut position = if self.entries.is_empty() {
            None
        } else {
            Some(self.position(hash, p.canonical, tag, bytes, b)?)
        };
        let existing = position
            .filter(|pos| self.entries[*pos].hash != 0)
            .map(|pos| self.entries[pos].name);
        if existing.is_none() && self.unique + 1 > self.entries.len() / 4 * 3 {
            self.grow_index(b)?;
            position = Some(self.position(hash, p.canonical, tag, bytes, b)?);
        }
        let position = position.ok_or(ResourceError::Invariant)?;
        let required = self
            .nodes
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        b.grow_vec(&mut self.nodes, required)?;
        b.grow_vec(&mut self.bytes, end)?;
        let canonical = existing.unwrap_or(slot);
        let offset = self.bytes.len() as u32;
        self.bytes.extend_from_slice(bytes);
        self.nodes.push(Name {
            tag,
            prefix: prefix.0,
            canonical,
            offset,
            len,
            depth,
        });
        // All failure points precede simultaneous raw/canonical publication.
        if existing.is_none() {
            self.entries[position] = Entry { hash, name: slot };
            self.unique += 1;
        }
        Ok(NameId(slot))
    }

    /// Root-to-leaf lexicographic order, never canonical-id order.
    /// No memo is created; both temporary paths are released before returning.
    /// Panics require whole-run discard, never reuse of an unwound ledger.
    #[allow(
        dead_code,
        reason = "Retained for component regressions and explicit internal inspection"
    )]
    pub(crate) fn compare(
        &self,
        a: NameId,
        c: NameId,
        b: &mut Budget,
    ) -> Result<Ordering, ResourceError> {
        b.charge_work(3)?; // comparison entry and two flat allocation releases
        let (x, y) = (self.get(a)?, self.get(c)?);
        if x.canonical == y.canonical {
            return Ok(Ordering::Equal);
        }
        let mut left = Vec::new();
        let mut right = Vec::new();
        let result = (|| {
            self.path(a, &mut left, b)?;
            self.path(c, &mut right, b)?;
            for (a, c) in left.iter().rev().zip(right.iter().rev()) {
                b.charge_work(1)?;
                let (x, y) = (self.get(*a)?, self.get(*c)?);
                let tag = x.tag.cmp(&y.tag);
                if tag != Ordering::Equal {
                    return Ok(tag);
                }
                if x.tag == 1 && x.len != y.len {
                    return Ok(x.len.cmp(&y.len));
                }
                b.charge_work(u64::from(x.len.min(y.len)) + 1)?;
                let order = self.payload(x).cmp(self.payload(y));
                if order != Ordering::Equal {
                    return Ok(order);
                }
            }
            Ok(left.len().cmp(&right.len()))
        })();
        let count = left.len() + right.len();
        release(left, b)?;
        release(right, b)?;
        b.release_frames(count)?;
        result
    }

    #[allow(
        dead_code,
        reason = "Name ordering component uses this path scratch; production integration is pending"
    )]
    fn path(
        &self,
        mut id: NameId,
        path: &mut Vec<NameId>,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        while id != NameId::ANONYMOUS {
            b.charge_work(1)?;
            let n = self.get(id)?;
            let len = path.len().checked_add(1).ok_or(ResourceError::Counter)?;
            b.reserve_frames(1)?;
            if let Err(e) = b.grow_vec(path, len) {
                b.release_frames(1)?;
                return Err(e);
            }
            path.push(id);
            id = NameId(n.prefix);
        }
        Ok(())
    }
}

impl LevelNames for Names {
    fn raw_summary(&self, id: NameId) -> Result<NameSummary, ResourceError> {
        let n = self.get(id)?;
        Ok(NameSummary {
            canonical: n.canonical,
            depth: n.depth,
        })
    }
}

impl OrderedLevelNames for Names {
    fn compare_names(
        &self,
        a: NameId,
        c: NameId,
        b: &mut Budget,
    ) -> Result<Ordering, ResourceError> {
        self.compare(a, c, b)
    }
}

fn release<T: Copy>(v: Vec<T>, b: &mut Budget) -> Result<(), ResourceError> {
    let bytes = v
        .capacity()
        .checked_mul(size_of::<T>())
        .ok_or(ResourceError::Counter)?;
    drop(v);
    b.release(bytes as u64)
}
