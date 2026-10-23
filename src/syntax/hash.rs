//! Deterministic, non-cryptographic hashing for kefir's own lookup tables.
//!
//! Every table that uses this hasher verifies full keys on a hash match, so a
//! collision costs probes, never a wrong answer. Probes are charged where the
//! tables charge them, so even adversarial collisions end in a resource stop,
//! not a verdict. The function is fixed (no per-process seed): equal inputs hash
//! equally in every run, mode and build, which keeps charges reproducible.
//!
//! Integers are absorbed whole with a multiply-rotate step; `finish` applies a
//! full 64-bit avalanche so the low bits used to index power-of-two tables
//! depend on every input bit.
use std::hash::Hasher;

const SEED: u64 = 0x243f_6a88_85a3_08d3;
const MULTIPLY: u64 = 0x9e37_79b9_7f4a_7c15;

#[derive(Clone, Copy)]
pub(crate) struct FastHasher(u64);

impl FastHasher {
    pub(crate) fn new() -> Self {
        Self(SEED)
    }

    fn absorb(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(23) ^ word).wrapping_mul(MULTIPLY);
    }
}

impl Default for FastHasher {
    fn default() -> Self {
        Self::new()
    }
}

impl Hasher for FastHasher {
    fn write(&mut self, bytes: &[u8]) {
        let (chunks, tail) = bytes.as_chunks::<8>();
        for chunk in chunks {
            self.absorb(u64::from_le_bytes(*chunk));
        }
        let mut last = [0u8; 8];
        last[..tail.len()].copy_from_slice(tail);
        // The tail length lands in the top byte, so inputs that differ only
        // by trailing zero bytes still differ.
        last[7] ^= tail.len() as u8;
        self.absorb(u64::from_le_bytes(last));
    }

    fn write_u8(&mut self, value: u8) {
        self.absorb(u64::from(value));
    }

    fn write_u16(&mut self, value: u16) {
        self.absorb(u64::from(value));
    }

    fn write_u32(&mut self, value: u32) {
        self.absorb(u64::from(value));
    }

    fn write_u64(&mut self, value: u64) {
        self.absorb(value);
    }

    fn write_usize(&mut self, value: usize) {
        self.absorb(value as u64);
    }

    fn finish(&self) -> u64 {
        let mut x = self.0;
        x ^= x >> 33;
        x = x.wrapping_mul(0xff51_afd7_ed55_8ccd);
        x ^= x >> 33;
        x = x.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
        x ^ (x >> 33)
    }
}
