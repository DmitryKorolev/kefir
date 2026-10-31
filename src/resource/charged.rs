//! Charged sizes: every build charges a stored value by its 64-bit layout.
//!
//! Budgets are semantics, so a 32-bit build must charge what a 64-bit
//! build charges, although its pointer-sized fields are smaller. Each charged type
//! declares its 64-bit size once here; on 64-bit targets a compile-time assertion
//! checks the declaration against `size_of`, so it cannot drift from the native layout.

/// A type whose values are charged to a budget.
pub(crate) trait Charged {
    /// Size of one value under the 64-bit layout.
    const BYTES: usize;
}

/// Bytes charged for one `T`.
#[inline(always)]
pub(crate) const fn bytes<T: Charged>() -> usize {
    T::BYTES
}

/// Declare the 64-bit size of charged types, asserted against `size_of` on 64-bit targets.
macro_rules! charged {
    ($($t:ty => $n:expr),* $(,)?) => {
        $(
            impl $crate::resource::charged::Charged for $t {
                const BYTES: usize = $n;
            }
            // A mismatch reports both sizes: "expected an array with a size of N,
            // found one with a size of M".
            #[cfg(target_pointer_width = "64")]
            const _: [(); $n] = [(); ::core::mem::size_of::<$t>()];
        )*
    };
}
pub(crate) use charged;

charged! {
    () => 0,
    u8 => 1,
    u16 => 2,
    u32 => 4,
    u64 => 8,
    usize => 8,
    i32 => 4,
    i64 => 8,
    bool => 1,
    char => 4,
    std::num::NonZeroU32 => 4,
    [u32; 2] => 8,
    [u32; 3] => 12,
    [u32; 4] => 16,
    [u32; 5] => 20,
    (u32, u32) => 8,
    (u32, u32, u32) => 12,
    std::sync::atomic::AtomicU64 => 8,
}
