//! Exact components of previously constructed keys, local to one Kernel attempt.
//! Callers keep evaluation representatives and typed tokens in separate tables.
//! Both the original environment and all its links persist for the entire
//! attempt. Retention never transfers these tables to a later attempt.

#[derive(Clone, Copy, Default)]
struct Row {
    mask: u64,
    env: u32,
    result: u32,
}

#[derive(Default)]
pub(super) struct ReadKeyCache([Row; 16]);

impl ReadKeyCache {
    fn index(env: u32, mask: u64) -> usize {
        let mixed =
            (mask ^ mask.rotate_right(23) ^ u64::from(env)).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        (mixed >> 60) as usize
    }

    /// Callers have already established a nonempty exact read mask.
    pub(super) fn get(&self, env: u32, mask: u64) -> Option<u32> {
        let row = self.0[Self::index(env, mask)];
        (mask != 0 && row.mask == mask && row.env == env).then_some(row.result)
    }

    pub(super) fn put(&mut self, env: u32, mask: u64, result: u32) {
        self.0[Self::index(env, mask)] = Row { mask, env, result };
    }
}

const _: () = assert!(size_of::<ReadKeyCache>() == 256);
