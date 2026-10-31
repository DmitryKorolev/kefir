//! wasm32 linear-memory layout, shared with `build.rs`, which passes it
//! to the linker for every wasm build so the stack guard and the stack agree.

/// Linear-memory stack: the checking thread's stack on wasm (`CHECK_STACK`).
pub(crate) const STACK_BYTES: u64 = 256 << 20;
/// Maximum linear memory: 64 MiB below 4 GiB. The stack is placed first, so an
/// overflow wraps below address 0 to the top of the 32-bit space; this gap keeps
/// any such frame outside memory, where the access traps instead of writing heap.
pub(crate) const MAX_MEMORY_BYTES: u64 = (4 << 30) - (64 << 20);
/// Initial linear memory: fewer `memory.grow` calls, each of which V8 accounts as
/// external memory and may answer with a garbage collection. Untouched pages cost
/// no resident memory.
pub(crate) const INITIAL_MEMORY_BYTES: u64 = 2 << 30;
