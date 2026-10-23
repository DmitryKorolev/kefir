//! Canonical manifest encoding. Membership/association remain caller
//! obligations; hashing supplied entries does not establish a complete build.
use crate::identity::sha256::{MessageTooLong, Sha256, hex};
use std::io::{self, Read, Write};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Domain {
    Specification,
    Build,
    ResourceProfile,
}
impl Domain {
    fn label(self) -> &'static [u8] {
        match self {
            Self::Specification => b"specification\n",
            Self::Build => b"build\n",
            Self::ResourceProfile => b"resource-profile\n",
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Kind {
    Source,
    Synthetic,
    Resource,
}
pub(crate) struct Entry<'a> {
    pub key: &'a str,
    pub digest: [u8; 32],
    pub kind: Kind,
}
#[derive(Debug)]
pub(crate) enum Error {
    Key,
    Namespace,
    Order,
    TooLong,
    #[allow(
        dead_code,
        reason = "Concrete build failure payload is retained in Debug diagnostics"
    )]
    Io(io::Error),
}
impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}
impl From<MessageTooLong> for Error {
    fn from(_: MessageTooLong) -> Self {
        Self::TooLong
    }
}

fn validate(domain: Domain, entry: &Entry<'_>) -> Result<(), Error> {
    let key = entry.key;
    if key.is_empty()
        || key.contains('\0')
        || std::path::Path::new(key).is_absolute()
        || key.split('/').any(|part| part == "." || part == "..")
    {
        return Err(Error::Key);
    }
    match (domain, entry.kind) {
        (Domain::Specification | Domain::Build, Kind::Source) if !key.starts_with('@') => Ok(()),
        (Domain::Build, Kind::Synthetic) if key.starts_with('@') => Ok(()),
        (Domain::ResourceProfile, Kind::Resource) if key.is_ascii() && !key.starts_with('@') => {
            Ok(())
        }
        _ => Err(Error::Namespace),
    }
}

/// Entries must be in strictly increasing UTF-8 byte order. Validate all entries
/// before writing anything; caller sorts and resolves membership independently.
/// Resource membership must be the exact profile table plus both revisions;
/// source digests must cover the actual input bytes, not Git identities. This
/// encoder cannot infer either fact from supplied keys/digests.
///
/// Output failure may leave a partial artifact, but returns NO digest. The caller
/// must discard that artifact; neither an I/O failure nor a caught panic licenses
/// using it as a manifest. Fixed scratch only; no allocation or checker budget.
/// The digest covers exactly the emitted bytes. For artifact association the
/// caller must own a fresh/truncated destination at position zero, with no stale
/// prefix/suffix or concurrent mutation; generic Write cannot establish this.
pub(crate) fn encode(
    domain: Domain,
    entries: &[Entry<'_>],
    output: &mut impl Write,
) -> Result<[u8; 32], Error> {
    let mut previous: Option<&[u8]> = None;
    for entry in entries {
        validate(domain, entry)?;
        if previous.is_some_and(|key| key >= entry.key.as_bytes()) {
            return Err(Error::Order);
        }
        previous = Some(entry.key.as_bytes());
    }
    let mut hash = Sha256::new();
    let mut emit = |bytes: &[u8]| -> Result<(), Error> {
        output.write_all(bytes)?;
        hash.update(bytes)?;
        Ok(())
    };
    emit(b"kefir-manifest-1\n")?;
    emit(domain.label())?;
    for entry in entries {
        let length = u64::try_from(entry.key.len()).map_err(|_| Error::TooLong)?;
        let mut decimal = [0; 20];
        emit(digits(length, &mut decimal))?;
        emit(b":")?;
        emit(entry.key.as_bytes())?;
        emit(b":")?;
        emit(&hex(&entry.digest))?;
        emit(b"\n")?;
    }
    output.flush()?;
    Ok(hash.finish()?)
}
fn digits(mut n: u64, buffer: &mut [u8; 20]) -> &[u8] {
    let mut cursor = 20;
    loop {
        cursor -= 1;
        buffer[cursor] = b'0' + (n % 10) as u8;
        n /= 10;
        if n == 0 {
            return &buffer[cursor..];
        }
    }
}

/// Hash actual reader bytes through clean EOF. Never turn an I/O error into a
/// digest of a readable prefix. Interrupted reads retry; other errors escape.
/// For a whole-source identity, the owner must supply the complete file from
/// position zero and prevent concurrent mutation; a subreader hashes only itself.
pub(crate) fn hash_reader(reader: &mut impl Read) -> Result<[u8; 32], Error> {
    let mut hash = Sha256::new();
    let mut buffer = [0; 4096];
    loop {
        match reader.read(&mut buffer) {
            Ok(0) => return Ok(hash.finish()?),
            Ok(n) => {
                let bytes = buffer
                    .get(..n)
                    .ok_or_else(|| Error::Io(io::ErrorKind::InvalidData.into()))?;
                hash.update(bytes)?;
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e.into()),
        }
    }
}
