//! Bucket accounting. No row or finalization is semantic evidence.
use crate::resource::{Bucket, Diagnostics, profile};

mod encode;
use crate::{
    syntax::levels::NameId,
    syntax::names::{
        Names,
        diagnostic::{Buffer, Span},
    },
};

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub(crate) struct Counts {
    /// input bytes, records, work, maximum global live capacity while active.
    pub accounting: [u64; 4],
    pub events: [u64; 11],
}
const _: () = assert!(std::mem::size_of::<Counts>() == 120);

#[derive(Clone, Copy, Default)]
/// Snapshots come from the same originating run's monotonic mandatory counters
/// and event accumulator. They are observations, never inputs to semantic work.
pub(crate) struct Point {
    pub additive: [u64; 3],
    pub events: [u64; 11],
    pub live: u64,
}

pub(crate) struct Declaration {
    pub ordinal: u64,
    pub name: Span,
    pub counts: Counts,
}
const _: () = assert!(std::mem::size_of::<Declaration>() == 136);

fn next_count(len: usize, ordinal: u64) -> Option<usize> {
    let next = len.checked_add(1)?;
    (ordinal == u64::try_from(next).ok()?
        && u64::try_from(next.checked_add(3)?).ok()? <= profile::DECLARATION_ENTRIES)
        .then_some(next)
}

pub(crate) struct Rows {
    fixed: [Counts; 3],
    declarations: Vec<Declaration>,
    names: Buffer,
    start: Point,
    peak: u64,
    active: usize,
    finished: bool,
    unavailable: bool,
    fixed_charged: bool,
}
impl Rows {
    pub(crate) fn new(d: &mut Diagnostics) -> Self {
        let fixed_charged = d.charge_work(1) && d.reserve(360);
        if !fixed_charged {
            d.allocation_failed();
        }
        Self {
            fixed: [Counts::default(); 3],
            declarations: Vec::new(),
            names: Buffer::default(),
            start: Point::default(),
            peak: 0,
            active: 2,
            finished: false,
            unavailable: !fixed_charged,
            fixed_charged,
        }
    }
}

/// Valid only while borrowed from a finalized owner. An external diagnostic
/// failure still invalidates all detail; the reporter must check the same ledger.
pub(crate) struct Detail<'a> {
    pub fixed: &'a [Counts; 3],
    pub declarations: &'a [Declaration],
    pub names: &'a Buffer,
}

impl Rows {
    /// One owner and one diagnostic ledger for the whole input. Never swap in a
    /// fresh ledger after failure or treat output selection as a semantic branch.
    fn usable(&mut self, d: &mut Diagnostics) -> bool {
        if self.unavailable || self.finished || d.events().is_none() {
            self.discard(d);
            false
        } else {
            true
        }
    }

    fn close(&mut self, point: Point, d: &mut Diagnostics) -> Option<()> {
        if !d.charge_work(1) {
            return None;
        }
        let counts = if self.active < 3 {
            self.fixed.get_mut(self.active)?
        } else {
            &mut self.declarations.get_mut(self.active - 3)?.counts
        };
        let mut next = *counts;
        for (index, value) in point.additive.into_iter().enumerate() {
            let delta = value.checked_sub(self.start.additive[index])?;
            next.accounting[index] = next.accounting[index].checked_add(delta)?;
        }
        for (index, value) in point.events.into_iter().enumerate() {
            let delta = value.checked_sub(self.start.events[index])?;
            next.events[index] = next.events[index].checked_add(delta)?;
        }
        next.accounting[3] = next.accounting[3].max(self.peak).max(point.live);
        *counts = next;
        self.start = point;
        self.peak = point.live;
        Some(())
    }

    /// Call after every successful semantic capacity reservation. Releases cannot
    /// increase the peak. Missed peaks cannot be recovered from final live bytes.
    pub(crate) fn observe_live(&mut self, live: u64, d: &mut Diagnostics) {
        if self.usable(d) {
            self.peak = self.peak.max(live);
        }
    }

    pub(crate) fn switch(&mut self, bucket: Bucket, point: Point, d: &mut Diagnostics) {
        if !self.usable(d) {
            return;
        }
        let next = match bucket {
            Bucket::Input => Some(0),
            Bucket::Report => Some(1),
            Bucket::Runtime => Some(2),
            Bucket::Declaration => self
                .declarations
                .len()
                .checked_sub(1)
                .and_then(|i| i.checked_add(3)),
        };
        match (self.close(point, d), next) {
            (Some(()), Some(next)) => self.active = next,
            _ => self.discard(d),
        }
    }

    pub(crate) fn declaration(
        &mut self,
        ordinal: u64,
        name: NameId,
        names: &Names,
        point: Point,
        d: &mut Diagnostics,
    ) {
        if !self.usable(d) {
            return;
        }
        let result = (|| {
            let next = next_count(self.declarations.len(), ordinal)?;
            self.close(point, d)?;
            let span = self.names.append(name, names, d)?;
            if !d.charge_work(1) || !d.grow_vec(&mut self.declarations, next) {
                return None;
            }
            self.declarations.push(Declaration {
                ordinal,
                name: span,
                counts: Counts::default(),
            });
            self.active = next + 2;
            Some(())
        })();
        if result.is_none() {
            self.discard(d);
        }
    }

    pub(crate) fn finish(&mut self, point: Point, d: &mut Diagnostics) -> Option<Detail<'_>> {
        if !self.usable(d) {
            return None;
        }
        if self.close(point, d).is_none() {
            self.discard(d);
            return None;
        }
        self.finished = true;
        Some(Detail {
            fixed: &self.fixed,
            declarations: &self.declarations,
            names: &self.names,
        })
    }

    /// Fixed rows occupy the owner until it is actually dropped. Their charge
    /// survives discard; only consuming retirement releases it.
    pub(crate) fn retire(mut self, d: &mut Diagnostics) {
        if self.finished && !self.unavailable {
            self.release_storage(d);
        } else {
            self.discard(d);
        }
        let fixed_charged = self.fixed_charged;
        drop(self);
        if fixed_charged {
            d.release(360);
        }
    }

    /// Ends this owner's epoch permanently and invalidates all name spans. Flat
    /// vectors are dropped before their diagnostic capacity is released.
    pub(crate) fn discard(&mut self, d: &mut Diagnostics) {
        self.unavailable = true;
        d.allocation_failed();
        self.release_storage(d);
    }

    fn release_storage(&mut self, d: &mut Diagnostics) {
        let declarations = std::mem::take(&mut self.declarations);
        let bytes = declarations.capacity() as u64 * std::mem::size_of::<Declaration>() as u64;
        drop(declarations);
        d.release(bytes);
        self.names.discard(d);
    }
}
