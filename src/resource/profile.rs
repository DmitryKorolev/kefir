//! Accepted profile values, shared by implemented limits and identity tooling.
//! Listed values do not imply that every governed subsystem is implemented.

pub(crate) const CACHE_BYTES_PER_SESSION: u64 = 1073741824;
pub(crate) const CHARGING_REVISION: u64 = 4;
pub(crate) const CHECKPOINT_REVISION: u64 = 2;
pub(crate) const CONTEXT_DEPTH: usize = 65536;
pub(crate) const COUNTER_MAX: u64 = 18446744073709551615;
pub(crate) const DECLARATION_ENTRIES: u64 = 16777216;
pub(crate) const DETAIL_NAME_FRAMES: u64 = 65537;
pub(crate) const DETAIL_WORK: u64 = 67108864;
pub(crate) const DIAGNOSTIC_LIVE_BYTES: u64 = 67108864;
pub(crate) const EMERGENCY_BYTES: u64 = 4096;
pub(crate) const INPUT_BYTES: u64 = 68_719_476_736;
pub(crate) const JSON_DEPTH: u32 = 128;
pub(crate) const MANAGED_LIVE_BYTES: u64 = 17179869184;
pub(crate) const READER_BUFFER_BYTES: usize = 65536;
pub(crate) const RECORD_BYTES: usize = 16777216;
pub(crate) const REDUCTION_PATH: u32 = 4194304;
pub(crate) const REPORT_BYTES: u64 = 1048576;
pub(crate) const STDERR_BYTES: u64 = 256;
pub(crate) const STRUCTURE_DEPTH: u32 = 65536;
pub(crate) const TABLE_ENTRIES_EACH: u64 = 4294967296;
pub(crate) const TERMINAL_WORK: u64 = 16777216;
pub(crate) const WORK_CHARGED: u64 = 281474976710656;
pub(crate) const WORKLIST_FRAMES: usize = 1048576;

// Ignored-test profile and build-time manifest inputs only. Production ENTRIES
// and every production limit remain unchanged; no runtime selector is shipped.
pub(crate) const BATCH_TEST_WORK: u64 = 2_000_000;
pub(crate) const BATCH_TEST_STORAGE: u64 = 16 * 1024 * 1024;
pub(crate) const BATCH_TEST_REDUCTION: u32 = 256;

pub(crate) const ENTRIES: [(&str, u64); 23] = [
    ("cache_bytes_per_session", CACHE_BYTES_PER_SESSION),
    ("charging_revision", CHARGING_REVISION),
    ("checkpoint_revision", CHECKPOINT_REVISION),
    ("context_depth", CONTEXT_DEPTH as u64),
    ("counter_max", COUNTER_MAX),
    ("declaration_entries", DECLARATION_ENTRIES),
    ("detail_name_frames", DETAIL_NAME_FRAMES),
    ("detail_work", DETAIL_WORK),
    ("diagnostic_live_bytes", DIAGNOSTIC_LIVE_BYTES),
    ("emergency_bytes", EMERGENCY_BYTES),
    ("input_bytes", INPUT_BYTES),
    ("json_depth", JSON_DEPTH as u64),
    ("managed_live_bytes", MANAGED_LIVE_BYTES),
    ("reader_buffer_bytes", READER_BUFFER_BYTES as u64),
    ("record_bytes", RECORD_BYTES as u64),
    ("reduction_path", REDUCTION_PATH as u64),
    ("report_bytes", REPORT_BYTES),
    ("stderr_bytes", STDERR_BYTES),
    ("structure_depth", STRUCTURE_DEPTH as u64),
    ("table_entries_each", TABLE_ENTRIES_EACH),
    ("terminal_work", TERMINAL_WORK),
    ("work_charged", WORK_CHARGED),
    ("worklist_frames", WORKLIST_FRAMES as u64),
];
