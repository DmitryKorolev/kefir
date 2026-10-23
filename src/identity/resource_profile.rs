//! Exact profile membership; this does not certify enforcement or a build.
use crate::identity::manifest::{self, Domain, Entry, Error, Kind};
use crate::identity::sha256::Sha256;
use crate::profile::ENTRIES;
use std::io::Write;

const _: () = assert!(std::mem::size_of::<Entry<'static>>() <= 64);

pub(crate) fn encode(output: &mut impl Write) -> Result<[u8; 32], Error> {
    encode_entries(ENTRIES, output)
}

pub(crate) fn encode_batch_test(output: &mut impl Write) -> Result<[u8; 32], Error> {
    encode_entries(
        ENTRIES.map(|(key, value)| {
            (
                key,
                match key {
                    "work_charged" => crate::profile::BATCH_TEST_WORK,
                    "managed_live_bytes" => crate::profile::BATCH_TEST_STORAGE,
                    "reduction_path" => crate::profile::BATCH_TEST_REDUCTION as u64,
                    _ => value,
                },
            )
        }),
        output,
    )
}

fn encode_entries(values: [(&str, u64); 23], output: &mut impl Write) -> Result<[u8; 32], Error> {
    // Fixed profile, fixed scratch: 23 inline entries (at most 1,472 bytes),
    // no owned heap or runtime per-record metadata. The output destination has
    // the same fresh-artifact ownership requirements as manifest::encode.
    let entries = values.map(|(key, value)| {
        let mut content = [0; 21];
        content[20] = b'\n';
        let mut cursor = 20;
        let mut n = value;
        loop {
            cursor -= 1;
            content[cursor] = b'0' + (n % 10) as u8;
            n /= 10;
            if n == 0 {
                break;
            }
        }
        let mut hash = Sha256::new();
        // A single <=21-byte input cannot reach SHA-256's bit-length bound.
        hash.update(&content[cursor..])
            .expect("bounded profile value");
        Entry {
            key,
            kind: Kind::Resource,
            digest: hash.finish().expect("bounded profile value"),
        }
    });
    manifest::encode(Domain::ResourceProfile, &entries, output)
}
