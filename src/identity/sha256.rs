//! Independently written byte-stream SHA-256 for identity tooling.
//! Equations/constants: FIPS 180-4 §§4.1.2,4.2.2,5.1.1,5.3.3,6.2.
//! No semantic checker, manifest membership decision or cryptographic certification.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct MessageTooLong;

pub(crate) struct Sha256 {
    state: [u32; 8],
    tail: [u8; 64],
    bytes: u64,
    used: u8,
    failed: bool,
}
const _: () = assert!(std::mem::size_of::<Sha256>() <= 120);
impl Sha256 {
    pub(crate) fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            tail: [0; 64],
            bytes: 0,
            used: 0,
            failed: false,
        }
    }

    /// The byte count excludes final padding and always fits the standard's
    /// 64-bit bit count. Overflow poisons the stream before processing any part
    /// of this update; ignoring the error cannot finalize a prefix digest.
    pub(crate) fn update(&mut self, mut input: &[u8]) -> Result<(), MessageTooLong> {
        if self.failed {
            return Err(MessageTooLong);
        }
        let total = u64::try_from(input.len())
            .ok()
            .and_then(|n| self.bytes.checked_add(n))
            .filter(|n| *n <= u64::MAX / 8);
        let Some(total) = total else {
            self.failed = true;
            return Err(MessageTooLong);
        };
        self.bytes = total;
        if self.used != 0 {
            let used = self.used as usize;
            let take = input.len().min(64 - used);
            self.tail[used..used + take].copy_from_slice(&input[..take]);
            self.used += take as u8;
            input = &input[take..];
            if self.used < 64 {
                return Ok(());
            }
            compress(&mut self.state, &self.tail);
            self.used = 0;
        }
        let (blocks, rest) = input.as_chunks::<64>();
        for block in blocks {
            compress(&mut self.state, block);
        }
        self.tail[..rest.len()].copy_from_slice(rest);
        self.used = rest.len() as u8;
        Ok(())
    }

    /// Consuming finalization prevents appending data to a padded stream.
    pub(crate) fn finish(mut self) -> Result<[u8; 32], MessageTooLong> {
        if self.failed {
            return Err(MessageTooLong);
        }
        let used = self.used as usize; // update leaves 0..=63 bytes pending.
        self.tail[used] = 0x80;
        self.tail[used + 1..].fill(0);
        if used >= 56 {
            compress(&mut self.state, &self.tail);
            self.tail.fill(0);
        }
        self.tail[56..].copy_from_slice(&(self.bytes * 8).to_be_bytes());
        compress(&mut self.state, &self.tail);
        let mut digest = [0; 32];
        for (word, output) in self.state.into_iter().zip(digest.as_chunks_mut::<4>().0) {
            output.copy_from_slice(&word.to_be_bytes());
        }
        Ok(digest)
    }
}

pub(crate) fn hex(digest: &[u8; 32]) -> [u8; 64] {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = [0; 64];
    for (byte, pair) in digest.iter().zip(output.as_chunks_mut::<2>().0) {
        pair[0] = DIGITS[(byte >> 4) as usize];
        pair[1] = DIGITS[(byte & 15) as usize];
    }
    output
}

fn compress(state: &mut [u32; 8], block: &[u8; 64]) {
    // All working storage is fixed: 256-byte schedule and eight u32 words.
    // These are build-tool computations, not semantic budget/counter events.
    let mut schedule = [0u32; 64];
    for (word, bytes) in schedule[..16].iter_mut().zip(block.as_chunks::<4>().0) {
        *word = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    }
    for i in 16..64 {
        let x = schedule[i - 15];
        let y = schedule[i - 2];
        let low = x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3);
        let high = y.rotate_right(17) ^ y.rotate_right(19) ^ (y >> 10);
        schedule[i] = schedule[i - 16]
            .wrapping_add(low)
            .wrapping_add(schedule[i - 7])
            .wrapping_add(high);
    }
    let mut words = *state;
    for (input, constant) in schedule.into_iter().zip(K) {
        let [a, b, c, d, e, f, g, h] = words;
        let upper = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let lower = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let choose = (e & f) ^ (!e & g);
        let majority = (a & b) ^ (a & c) ^ (b & c);
        let right = h
            .wrapping_add(upper)
            .wrapping_add(choose)
            .wrapping_add(constant)
            .wrapping_add(input);
        let left = lower.wrapping_add(majority);
        words = [
            right.wrapping_add(left),
            a,
            b,
            c,
            d.wrapping_add(right),
            e,
            f,
            g,
        ];
    }
    for (out, word) in state.iter_mut().zip(words) {
        *out = out.wrapping_add(word);
    }
}

// Standardized mathematical constants, not copied implementation code.
const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];
