//! Wide dependency-sensitive ordinary evaluation keys.
use super::*;

pub(super) type RepresentativeKey = ([u64; 4], [u32; 16]);
const _: () = assert!(size_of::<Map<RepresentativeKey, u32>>() <= 64);
const _: () = assert!(size_of::<(RepresentativeKey, u32)>() <= 104);

impl Kernel<'_, '_> {
    /// Called after an exact miss, for ordinary sources with loose range 64–256,
    /// no Free variables/checked context, and the existing activation work.
    /// Equal exact source and universes fix the referenced positions. Raw value
    /// IDs preserve denotation when forced. Later LamTy inference additionally
    /// relies on the checked-entry valid-annotation/NONE premise;
    /// this key does not certify an arbitrary internal environment's types.
    pub(super) fn wide_evaluation_read_key(&mut self, e: ExprId, env: u32) -> R<(u32, u32, u32)> {
        let original = (3, env, 0);
        // None is incomplete eligibility, never equality. Every error, including
        // an inherited Abort, propagates; there is no new local allowance.
        let plan = if let Some(&plan) = self.read_plans.get(&e.slot()) {
            plan
        } else {
            // A direct beta step can expose a much smaller source. Avoid
            // recursively preparing a new plan for its lambda body first.
            // This is only a sharing refusal, never a failed equality fact.
            let kind = self
                .exprs
                .get(e, self.b)?
                .kind(self.exprs, self.levels, self.b)?;
            if let ExprKind::App(f, _) = kind
                && matches!(
                    self.exprs
                        .get(f, self.b)?
                        .kind(self.exprs, self.levels, self.b)?,
                    ExprKind::Lambda(..)
                )
            {
                return Ok(original);
            }
            self.read_plan(e)?
        };
        let Some(mask) = plan else {
            return Ok(original);
        };
        let reads = mask.iter().map(|word| word.count_ones()).sum::<u32>();
        if !(1..=16).contains(&reads) {
            return Ok(original);
        }
        let highest = mask
            .iter()
            .enumerate()
            .rev()
            .find(|(_, word)| **word != 0)
            .map_or(0, |(i, word)| i as u32 * 64 + 64 - word.leading_zeros());
        // One upfront charge covers a single streaming parent walk and value
        // collection, even on a miss or failed capture. No per-hop Budget calls.
        self.steps_by(u64::from(highest + reads))?;
        let mut walk = env;
        let mut values = [0; 16];
        let mut used = 0;
        for position in 0..highest {
            if walk == 0 {
                return Ok(original);
            }
            let node = self.envs[walk as usize];
            if mask[(position / 64) as usize] & (1u64 << (position % 64)) != 0 {
                values[used] = node.val;
                used += 1;
            }
            walk = node.parent;
        }
        // Full memo-key equality checks both values, exact source and universes;
        // a hash collision never supplies an equality or checkedness fact.
        if reads <= 2 {
            return Ok((reads, values[0], values[1]));
        }
        let key = (mask, values);
        // Full Eq compares all four mask words and all sixteen value slots;
        // unused slots are zero-filled. Look up before testing the shared cap,
        // so saturation loses only new opportunities, never existing facts.
        if let Some(&representative) = self.wide_read_environments.get(&key) {
            return Ok((3, representative, 0));
        }
        if self.read_environments.len() + self.wide_read_environments.len() < 131_072 {
            self.insert_wide_read_environment(key, env)?;
        }
        Ok(original)
    }

    /// Generic exact-table admission includes physical rehash overlap. Failed
    /// operations keep all successful reservations with normal cleanup.
    fn insert_wide_read_environment(&mut self, key: RepresentativeKey, env: u32) -> R<()> {
        map_put(
            self.b,
            &mut self.reserved,
            &mut self.wide_read_environments,
            key,
            env,
        )
    }
}
