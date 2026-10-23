//! Candidate build membership. Compiler dependency coverage and stable inputs
//! remain external association gates; this module cannot identify an execution.
use crate::identity::manifest::{self, Domain, Entry, Kind};
use std::{collections::BTreeMap, fs, io, path::Path};

#[derive(Debug)]
pub(crate) enum Error {
    #[allow(
        dead_code,
        reason = "Concrete build failure payload is retained in Debug diagnostics"
    )]
    Io(io::Error),
    Member,
    #[allow(
        dead_code,
        reason = "Concrete build failure payload is retained in Debug diagnostics"
    )]
    Manifest(manifest::Error),
}
impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}
impl From<manifest::Error> for Error {
    fn from(error: manifest::Error) -> Self {
        Self::Manifest(error)
    }
}

pub(crate) struct Inputs {
    files: BTreeMap<String, [u8; 32]>,
}
impl Inputs {
    #[allow(
        dead_code,
        reason = "Used by build.rs dependency directives; shared identity tests do not call it"
    )]
    pub(crate) fn files(&self) -> &BTreeMap<String, [u8; 32]> {
        &self.files
    }

    fn file(&mut self, root: &Path, key: String) -> Result<(), Error> {
        // Keys are also emitted through Cargo's line-based rerun protocol.
        // Manifest length-prefixing alone does not prevent directive injection.
        if key.contains(['\r', '\n']) {
            return Err(Error::Member);
        }
        let path = root.join(&key);
        if !fs::symlink_metadata(&path)?.file_type().is_file() {
            return Err(Error::Member);
        }
        let digest = manifest::hash_reader(&mut fs::File::open(path)?)?;
        if self.files.insert(key, digest).is_some() {
            return Err(Error::Member);
        }
        Ok(())
    }

    fn directory(&mut self, root: &Path, key: &str) -> Result<(), Error> {
        let path = root.join(key);
        if !fs::symlink_metadata(&path)?.file_type().is_dir() {
            return Err(Error::Member);
        }
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let name = entry.file_name().into_string().map_err(|_| Error::Member)?;
            let child = format!("{key}/{name}");
            if entry.file_type()?.is_dir() {
                self.directory(root, &child)?;
            } else {
                self.file(root, child)?;
            }
        }
        Ok(())
    }

    /// Own the same specification bytes already inspected by the selector.
    /// Root/directory membership and bytes must remain stable through compilation;
    /// rehashing once is not a snapshot and does not prove compiler consumption.
    pub(crate) fn collect(
        root: &Path,
        specification: &crate::identity::specification::Selection,
    ) -> Result<Self, Error> {
        let mut inputs = Self {
            files: BTreeMap::new(),
        };
        for key in [
            "build.rs",
            "Cargo.toml",
            "Cargo.lock",
            "rust-toolchain.toml",
        ] {
            inputs.file(root, key.to_owned())?;
        }
        inputs.directory(root, "src")?;
        for required in ["src/lib.rs", "src/main.rs"] {
            if !inputs.files.contains_key(required) {
                return Err(Error::Member);
            }
        }
        for source in specification.sources() {
            if inputs
                .files
                .insert(source.key.clone(), source.digest)
                .is_some()
            {
                return Err(Error::Member);
            }
        }
        Ok(inputs)
    }

    /// Values are exact bytes, without implicit separators or newline rewriting.
    /// All settings must be observed by the build owner, never caller placeholders.
    pub(crate) fn encode(
        &self,
        settings: Settings<'_>,
        output: &mut impl io::Write,
    ) -> Result<[u8; 32], Error> {
        let mut entries = Vec::new();
        for (key, bytes) in [
            ("@features", settings.features),
            ("@profile", settings.profile),
            ("@resource-profile", settings.resource),
            ("@rustc-version", settings.rustc),
            ("@specification", settings.specification),
            ("@target", settings.target),
        ] {
            if bytes.is_empty() {
                return Err(Error::Member);
            }
            entries.push(Entry {
                key,
                digest: manifest::hash_reader(&mut &*bytes)?,
                kind: Kind::Synthetic,
            });
        }
        entries.extend(self.files.iter().map(|(key, digest)| Entry {
            key,
            digest: *digest,
            kind: Kind::Source,
        }));
        entries.sort_unstable_by(|a, b| a.key.cmp(b.key));
        Ok(manifest::encode(Domain::Build, &entries, output)?)
    }
}

pub(crate) struct Settings<'a> {
    pub features: &'a [u8],
    pub profile: &'a [u8],
    pub resource: &'a [u8],
    pub rustc: &'a [u8],
    pub specification: &'a [u8],
    pub target: &'a [u8],
}
