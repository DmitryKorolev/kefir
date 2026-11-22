//! Attempt-local ownership of replayable arithmetic results.
use super::*;

#[derive(Clone, Copy)]
pub(super) struct Recipe {
    pub(super) op: Operation,
    pub(super) left: u32,
    pub(super) right: u32,
}

struct Resident {
    recipe: Recipe,
    id: u32,
    bytes: u64,
}

crate::resource::charged::charged! { Resident => 24 }

#[derive(Default)]
pub(super) struct Store {
    entries: Vec<Resident>,
    clock: u64,
    bytes: u64,
    power_bytes: u64,
    power_slots: usize,
}

// Memory threshold uses portable charged bytes, including the retained backend
// envelope. An oversize operand (and its pinned partner) may be live while used.
const BYTES: u64 = 16 << 20;
const SLOTS: usize = 256;
const PREFERRED_POWER_BYTES: u64 = BYTES / 4;
const PREFERRED_POWER_SLOTS: usize = SLOTS / 16;

impl Kernel<'_, '_> {
    /// Input IDs name earlier completed naturals in this graph (NONE denotes zero).
    /// Only the payload reservation is evictable. Table growth stays with the graph.
    pub(super) fn store_product(&mut self, recipe: Recipe) -> R<u32> {
        let before = self.reserved;
        let r = computed_nat(
            recipe.op,
            nat_literal(&self.nats, recipe.left),
            nat_literal(&self.nats, recipe.right),
            self.b,
            &mut self.reserved,
        )?;
        if !matches!(r, NatLit::Computed(..)) {
            return self.nat(r);
        }
        let bytes = self.reserved - before;
        let id = self.nats.len() as u32;
        let v = self.nat(r)?;
        self.remember_natural(id, recipe, bytes, NONE)?;
        self.observe_natural(id, NONE)?;
        Ok(v)
    }
    pub(super) fn adjacent_computed(&mut self, id: u32, op: Operation) -> R<u32> {
        let one = self.nat(NatLit::Small(1))?;
        let Val::Nat(right) = self.vals[one as usize] else {
            return Err(ResourceError::Invariant.into());
        };
        self.store_product(Recipe {
            op,
            left: id,
            right,
        })
    }
    pub(super) fn predecessor_value(&mut self, id: u32) -> R<u32> {
        self.observe_natural(id, NONE)?;
        if matches!(self.nats[id as usize], NatLit::Computed(..)) {
            return self.adjacent_computed(id, Operation::Sub);
        }
        let n = nat_pred(&self.nats[id as usize], self.b, &mut self.reserved)?;
        self.nat(n)
    }

    pub(super) fn remember_natural(
        &mut self,
        id: u32,
        recipe: Recipe,
        bytes: u64,
        pin: u32,
    ) -> R<()> {
        let store = &mut self.natural_store;
        let power = recipe.op == Operation::Pow;
        while !store.entries.is_empty()
            && (store.entries.len() >= SLOTS || store.bytes + bytes > BYTES)
        {
            self.b.charge_work(store.entries.len() as u64)?;
            let prefer_powers = store.power_slots != 0
                && store.power_slots + usize::from(power) <= PREFERRED_POWER_SLOTS
                && store.power_bytes + if power { bytes } else { 0 } <= PREFERRED_POWER_BYTES;
            let mut oldest = None;
            for (index, entry) in store.entries.iter().enumerate() {
                if entry.id == pin {
                    continue;
                }
                let NatLit::Computed(_, touched) = &self.nats[entry.id as usize] else {
                    return Err(ResourceError::Invariant.into());
                };
                let order = (
                    prefer_powers && entry.recipe.op == Operation::Pow,
                    touched.get(),
                );
                if oldest.is_none_or(|(_, current)| order < current) {
                    oldest = Some((index, order));
                }
            }
            let Some((index, _)) = oldest else { break };
            let entry = store.entries.swap_remove(index);
            self.nats[entry.id as usize] = NatLit::Evicted(entry.recipe);
            self.b.release(entry.bytes)?;
            self.reserved = self
                .reserved
                .checked_sub(entry.bytes)
                .ok_or(ResourceError::Invariant)?;
            store.bytes -= entry.bytes;
            if entry.recipe.op == Operation::Pow {
                store.power_bytes -= entry.bytes;
                store.power_slots -= 1;
            }
        }
        room(self.b, &mut self.reserved, &mut store.entries, 1)?;
        store.entries.push(Resident { id, recipe, bytes });
        store.bytes += bytes;
        if power {
            store.power_bytes += bytes;
            store.power_slots += 1;
        }
        Ok(())
    }

    pub(super) fn observe_natural(&mut self, id: u32, pin: u32) -> R<()> {
        if id == NONE {
            return Ok(());
        }
        if let NatLit::Evicted(recipe) = self.nats[id as usize] {
            let old = self.reserved;
            let value = replay(&self.nats, recipe, self.b, &mut self.reserved, 0)?;
            if !matches!(value, NatLit::Computed(..)) {
                return Err(ResourceError::Invariant.into());
            }
            self.nats[id as usize] = value;
            self.remember_natural(id, recipe, self.reserved - old, pin)?;
        }
        if let NatLit::Computed(_, touched) = &self.nats[id as usize] {
            self.natural_store.clock = self
                .natural_store
                .clock
                .checked_add(1)
                .ok_or(ResourceError::Counter)?;
            touched.set(self.natural_store.clock);
        }
        Ok(())
    }

    pub(super) fn observe_pair(&mut self, a: u32, b: u32) -> R<()> {
        self.observe_natural(a, b)?;
        self.observe_natural(b, a)
    }
}

fn replay(
    nats: &[NatLit],
    recipe: Recipe,
    b: &mut Budget,
    retained: &mut u64,
    depth: u32,
) -> R<NatLit> {
    if depth == 32 {
        return Err(KErr::Abort);
    }
    b.charge_work(1)?;
    let mut tmp = 0;
    let result = (|| {
        let mut operand = |id| -> R<Option<NatLit>> {
            match nat_literal(nats, id) {
                NatLit::Evicted(r) => replay(nats, *r, b, &mut tmp, depth + 1).map(Some),
                _ => Ok(None),
            }
        };
        let left = operand(recipe.left)?;
        if recipe.left == recipe.right {
            let value = left
                .as_ref()
                .unwrap_or_else(|| nat_literal(nats, recipe.left));
            return computed_nat(recipe.op, value, value, b, retained);
        }
        let right = operand(recipe.right)?;
        computed_nat(
            recipe.op,
            left.as_ref()
                .unwrap_or_else(|| nat_literal(nats, recipe.left)),
            right
                .as_ref()
                .unwrap_or_else(|| nat_literal(nats, recipe.right)),
            b,
            retained,
        )
    })();
    b.release(tmp)?;
    result
}
impl Store {
    pub(super) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}
