//! Public snapshot specification membership; build-time only.
use crate::identity::manifest::{self, Domain, Entry, Kind};
use std::{fs, io, path::Path};

pub(crate) const LOCK_FILE: &str = "specification.lock";

#[derive(Debug)]
pub(crate) enum Error {
    #[allow(
        dead_code,
        reason = "Build failure payload is retained in Debug diagnostics"
    )]
    Io(io::Error),
    Source,
    #[allow(
        dead_code,
        reason = "Build failure payload is retained in Debug diagnostics"
    )]
    Manifest(manifest::Error),
}
impl From<io::Error> for Error {
    fn from(value: io::Error) -> Self {
        Self::Io(value)
    }
}
impl From<manifest::Error> for Error {
    fn from(value: manifest::Error) -> Self {
        Self::Manifest(value)
    }
}
pub(crate) struct Source {
    pub key: String,
    pub digest: [u8; 32],
}
pub(crate) struct Selection {
    sources: Vec<Source>,
}
impl Selection {
    pub(crate) fn sources(&self) -> &[Source] {
        &self.sources
    }
    pub(crate) fn encode(&self, out: &mut impl io::Write) -> Result<[u8; 32], Error> {
        let entries: Vec<_> = self
            .sources
            .iter()
            .map(|source| Entry {
                key: &source.key,
                digest: source.digest,
                kind: Kind::Source,
            })
            .collect();
        Ok(manifest::encode(Domain::Specification, &entries, out)?)
    }

    pub(crate) fn write_lock(&self, out: &mut impl io::Write) -> Result<(), Error> {
        writeln!(out, "kefir-specification-lock-1")?;
        for source in &self.sources {
            let hex: String = source
                .digest
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect();
            writeln!(out, "included {hex} {}", source.key)?;
        }
        Ok(())
    }
}
pub(crate) fn select(root: &Path) -> Result<Selection, Error> {
    let mut sources = Vec::new();
    for key in ["README.md", "release-manifest.json"] {
        let path = root.join(key);
        if !fs::symlink_metadata(&path)?.file_type().is_file() {
            return Err(Error::Source);
        }
        sources.push(Source {
            key: key.to_owned(),
            digest: manifest::hash_reader(&mut fs::File::open(path)?)?,
        });
    }
    Ok(Selection { sources })
}
