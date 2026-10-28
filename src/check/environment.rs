//! Validated templates and private signature staging.
//! Publication is module-private: decoded Requests cannot install themselves.
use crate::decode::primitive_decode::declarations::{Hint, Kind, Request, Safety};
use crate::resource::{Budget, Event, ResourceError};
use crate::syntax::expressions::ExprId;
use crate::syntax::levels::{LevelNames, NameId};
use crate::syntax::names::Names;
use std::{mem::size_of, num::NonZeroU32};

/// Zero-sized trusted-construction authority for checkedness
/// certificates minted by the environment machinery (completed inferences,
/// scheme formation, comparison-established binder domains). The field is
/// private and the mint is module-private, so only code inside
/// `crate::check::environment` — including its descendant modules — can
/// construct it; out-of-region minting is a compile error. The exhaustive
/// production mint list is `scripts/check_checked_mint_sites.py`.
pub(crate) struct CheckednessMint(());
impl CheckednessMint {
    fn mint() -> Self {
        Self(())
    }
}

mod annotations;
mod constant_use;
mod finite;
pub(crate) mod kernel;
pub(crate) use finite::{FiniteRequest, Referent as FiniteReferent};
pub(crate) mod instantiation;
mod native_natural;
pub(crate) mod natural;
mod predicates;
mod quotient;
mod string;
mod unsafe_candidate;
use crate::decode::primitive_decode::quotients::Role as QuotientRole;
mod nullary;
use nullary::{ConstructorRecord, FamilyRecord, RecursorRecord};
pub(crate) use nullary::{NullaryMetadata, NullaryRule};

pub(crate) mod normalization;

pub(crate) mod validation;

/// Internal storage kinds are not input declaration kinds or axiom policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SignatureKind {
    Inductive,
    Constructor,
    Recursor,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StoredKind {
    Ordinary(Kind),
    Signature(SignatureKind),
    Quotient(QuotientRole),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TypeSource {
    Original(ExprId),
    /// Slot owned by the active auxiliary phase, never an imported template.
    Auxiliary(u32),
    Quotient(QuotientRole),
}
pub(crate) struct ConstantSignature<'a> {
    // Present only on a lookup into this fixed validated environment prefix.
    pub slot: Option<u32>,
    pub kind: StoredKind,
    pub name: NameId,
    pub parameters: &'a [NameId],
    pub ty: TypeSource,
    pub value: Option<ExprId>,
    pub all: &'a [NameId],
    pub safety: Safety,
    pub hint: Option<Hint<'a>>,
}
/// Only the validator may submit a checked original signature to staging.
struct SignatureInput<'a> {
    kind: SignatureKind,
    name: NameId,
    parameters: &'a [NameId],
    ty: ExprId,
    all: &'a [NameId],
}
/// Opaque capability for one immutable checked-signature prefix, in this owner.
/// Origin is session-local; copying a token does not extend its phase lifetime.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
/// Same-owner construction premise: this token is used only with the
/// Environment/State that minted it. Epoch/frontier checks detect stale phases
/// within that owner; they do not brand or detect cross-owner token replay.
pub(crate) struct Formation {
    epoch: NonZeroU32,
    before: u32,
}
impl Formation {
    pub(crate) fn before(self) -> usize {
        self.before as usize
    }
}
#[derive(Clone, Copy)]
struct AuxiliaryTemplates {
    expression_end: u32,
    level_end: NonZeroU32,
}
const _: () = assert!(size_of::<Option<AuxiliaryTemplates>>() == 8);
#[derive(Clone, Copy)]
struct Stage {
    phase: Formation,
    expression_end: u32,
    level_end: u32,
    auxiliary: Option<AuxiliaryTemplates>,
}
struct PreparedCommit<'a> {
    environment: &'a mut Environment,
    natural: natural::Certificate,
}
impl PreparedCommit<'_> {
    /// The caller has completed exact matching, rule checks and scratch cleanup.
    /// A dropped token leaves the stage private; commit performs no fallible work.
    fn with_natural(mut self, natural: natural::Certificate) -> Self {
        self.natural = natural;
        self
    }
    fn commit(self) {
        if self.natural.0[0] != 0 {
            self.environment.natural = self.natural;
        }
        self.environment.committed = self.environment.entries.len() as u32;
        self.environment.stage = None;
    }
}
const _: () = assert!(size_of::<Formation>() == 8);
const _: () = assert!(size_of::<Option<Stage>>() == 24);

#[derive(Clone, Copy, Default)]
struct Span {
    offset: u32,
    len: u32,
}
#[derive(Clone, Copy)]
enum StoredHint {
    None,
    Opaque,
    Abbrev,
    Regular(Span),
}
#[derive(Clone, Copy)]
struct Template {
    name: NameId,
    // Interpreted only with kind: original slot, or inert quotient payload.
    type_slot: u32,
    value: Option<ExprId>,
    parameters: Span,
    all: Span,
    hint: StoredHint,
    kind: StoredKind,
    safety: Safety,
}
const _: () = assert!(size_of::<Template>() == 48);

/// Every usable entry must have completed all semantic obligations before
/// publication. `publish_validated` is private to this module and its validator child;
/// no public or crate-wide raw-request installer exists. Storage-only unit tests
/// bypass validation explicitly; the validator child establishes supported typing.
/// Committed entries are fully checked. Inductive stages have checked-signature
/// authority; the unsafe-body phase alone also exposes its full candidate.
/// All retained roots are original decoded syntax.
/// State owns failure poisoning and retires every capacity, including abandoned
/// staging suffixes. No staged candidate grants an ordinary installed fact or
/// a safe-mode premise; signature staging grants no computation.
#[derive(Default)]
pub(crate) struct Environment {
    entries: Vec<Template>,
    by_name: Vec<u32>, // 0 absent; declaration slot + 1 otherwise
    names: Vec<NameId>,
    hints: Vec<u8>,
    constructors: Vec<ConstructorRecord>,
    recursors: Vec<RecursorRecord>,
    families: Vec<FamilyRecord>,
    rules: Vec<NullaryRule>,
    natural: natural::Certificate,
    native_natural: native_natural::Certificate,
    predicates: predicates::Certificate,
    string: string::Certificate,
    finite: finite::Certificate,
    quotient: Option<quotient::Package>,
    annotation_identity: [u32; 4], // committed slot + 1; zero means uncertified
    committed: u32,
    epoch: u32,
    stage: Option<Stage>,
    /// Run-lifetime "no rule" memo: one bit per canonical name key,
    /// covering `by_name`. A set bit means a full-allowance derivation of that
    /// constant found no rule; it only withholds an optional derivation, and
    /// no result, equality or failure is concluded from it. Scope: this run's
    /// environment, all declarations, attempts and modes; bits are never
    /// cleared, so a stale bit (a retired staged name) costs speed only.
    no_rule: Vec<std::sync::atomic::AtomicU64>,
}
// Nine Vec headers (the last the no-rule memo) and the phase/frontier
// state retain only original roots.
// Fixed certificates include the160-byte remaining-Nat certificate, for 744 bytes
// total. Entry layout remains48bytes; no per-declaration stage/certificate field.
const _: () = assert!(size_of::<Environment>() == 744);
// Preparation-only, same-owner checkpoint minted before begin_stage. It cannot
// authorize publication or generated-root lookup; it only bounds retirement.
struct SignatureStageCheckpoint {
    metadata: [usize; 4],
    committed: u32,
    epoch: u32,
}
const _: () = assert!(size_of::<SignatureStageCheckpoint>() == 40);
impl Environment {
    /// Whether the memo records no rule for canonical name `canon`.
    pub(crate) fn no_rule(&self, canon: u32) -> bool {
        use std::sync::atomic::Ordering::Relaxed;
        self.no_rule
            .get(canon as usize / 64)
            .is_some_and(|w| w.load(Relaxed) >> (canon % 64) & 1 == 1)
    }
    /// Record no rule for `canon`; a name outside `by_name` is not recorded.
    pub(crate) fn set_no_rule(&self, canon: u32) {
        use std::sync::atomic::Ordering::Relaxed;
        // One checking thread at a time owns the environment; a load and a
        // store (not a read-modify-write) suffice.
        if let Some(w) = self.no_rule.get(canon as usize / 64) {
            w.store(w.load(Relaxed) | 1 << (canon % 64), Relaxed);
        }
    }
    pub(crate) fn len(&self) -> usize {
        self.committed as usize
    }

    /// Ordinary visibility only: `before` is the current declaration's immutable
    /// prior-environment frontier, captured by its validator. A future frontier
    /// is an invariant failure, never permission to see a pending declaration.
    /// This view grants neither unfolding permission nor an instantiated type.
    pub(crate) fn lookup(
        &self,
        name: NameId,
        before: usize,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Option<ConstantSignature<'_>>, ResourceError> {
        self.lookup_visible(name, before, None, names, b)
    }
    fn lookup_visible(
        &self,
        name: NameId,
        before: usize,
        formation: Option<Formation>,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Option<ConstantSignature<'_>>, ResourceError> {
        // Counts a requested environment lookup even when subsequent
        // work/visibility/origin checks fail. Dense-index reads are not events.
        b.observe(Event::EnvironmentLookups, 1);
        b.charge_work(1)?;
        self.check_visibility(before, formation)?;
        let key = names.summary(name, b)?.canonical as usize;
        let encoded = self.by_name.get(key).copied().unwrap_or(0);
        if encoded == 0 || encoded as usize > before {
            return Ok(None);
        }
        let entry = self
            .entries
            .get(encoded as usize - 1)
            .ok_or(ResourceError::Invariant)?;
        Ok(Some(ConstantSignature {
            slot: Some(encoded - 1),
            kind: entry.kind,
            name: entry.name,
            parameters: view(&self.names, entry.parameters)?,
            ty: match entry.kind {
                StoredKind::Quotient(role) => TypeSource::Quotient(role),
                StoredKind::Signature(_)
                    if encoded as usize > self.len()
                        && self.stage.is_some_and(|stage| stage.auxiliary.is_some()) =>
                {
                    TypeSource::Auxiliary(entry.type_slot)
                }
                _ => TypeSource::Original(ExprId::from_stored_original(entry.type_slot)),
            },
            value: entry.value,
            all: view(&self.names, entry.all)?,
            safety: entry.safety,
            hint: match entry.hint {
                StoredHint::None => None,
                StoredHint::Opaque => Some(Hint::Opaque),
                StoredHint::Abbrev => Some(Hint::Abbrev),
                StoredHint::Regular(span) => Some(Hint::Regular(view(&self.hints, span)?)),
            },
        }))
    }

    /// ONLY the owning semantic validator may call this after kind-specific
    /// type/body/scope/policy/metadata validation. Original raw
    /// fields are retained, never generated inference/theorem-copy results.
    /// A duplicate or malformed body shape here is an invariant failure: the
    /// validator must classify those before requesting publication. Failure
    /// publishes no entry, index mapping or side-store payload; grown capacity
    /// may remain owned and charged. No failure point follows first mutation.
    fn publish_validated(
        &mut self,
        request: &Request<'_>,
        names: &Names,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        b.charge_work(1)?;
        if self.stage.is_some()
            || self.entries.len() != self.len()
            || (request.kind == Kind::Axiom) != request.value.is_none()
        {
            return Err(ResourceError::Invariant);
        }
        self.append_entry(
            &ConstantSignature {
                slot: None,
                kind: StoredKind::Ordinary(request.kind),
                name: request.name,
                parameters: request.parameters,
                ty: TypeSource::Original(request.ty),
                value: request.value,
                all: request.all,
                safety: request.safety,
                hint: request.hint,
            },
            names,
            b,
        )?;
        self.committed = self.entries.len() as u32;
        Ok(())
    }
    fn append_entry(
        &mut self,
        request: &ConstantSignature<'_>,
        names: &Names,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        let key = names.summary(request.name, b)?.canonical as usize;
        if self.by_name.get(key).copied().unwrap_or(0) != 0 {
            return Err(ResourceError::Invariant);
        }
        let needed = self
            .entries
            .len()
            .checked_add(1)
            .ok_or(ResourceError::Counter)?;
        let encoded = crate::resource::traced!("environment.slot_limit", needed, {
            u32::try_from(needed).map_err(|_| ResourceError::Storage)
        })?;
        let parameters = span(self.names.len(), request.parameters.len())?;
        let all = span(
            self.names
                .len()
                .checked_add(request.parameters.len())
                .ok_or(ResourceError::Counter)?,
            request.all.len(),
        )?;
        let name_end = all.offset as usize + all.len as usize;
        let bytes = match request.hint {
            Some(Hint::Regular(bytes)) => bytes,
            _ => &[],
        };
        let hint_span = span(self.hints.len(), bytes.len())?;
        let hint_end = hint_span.offset as usize + hint_span.len as usize;
        let index_end = self
            .by_name
            .len()
            .max(key.checked_add(1).ok_or(ResourceError::Counter)?);
        // Coarse known spans cover copies and index zero-fill, without per-byte
        // accounting. The dense index costs four bytes per covered raw name slot.
        let copied = request
            .parameters
            .len()
            .checked_add(request.all.len())
            .and_then(|n| n.checked_add(bytes.len()))
            .and_then(|n| n.checked_add(index_end - self.by_name.len()))
            .ok_or(ResourceError::Counter)?;
        b.charge_work(copied as u64 + 1)?;
        b.grow_vec(&mut self.entries, needed)?;
        b.grow_vec(&mut self.by_name, index_end)?;
        b.grow_vec(&mut self.names, name_end)?;
        b.grow_vec(&mut self.hints, hint_end)?;
        b.grow_vec(&mut self.no_rule, index_end.div_ceil(64))?;
        let type_slot = match (request.kind, request.ty) {
            (StoredKind::Quotient(a), TypeSource::Quotient(b)) if a == b => 0,
            (StoredKind::Signature(_), TypeSource::Auxiliary(slot))
                if self
                    .stage
                    .and_then(|stage| stage.auxiliary)
                    .is_some_and(|templates| slot < templates.expression_end) =>
            {
                slot
            }
            (StoredKind::Ordinary(_) | StoredKind::Signature(_), TypeSource::Original(ty)) => {
                ty.slot()
            }
            _ => return Err(ResourceError::Invariant),
        };
        let entry = Template {
            name: request.name,
            type_slot,
            value: request.value,
            parameters,
            all,
            kind: request.kind,
            safety: request.safety,
            hint: match request.hint {
                None => StoredHint::None,
                Some(Hint::Opaque) => StoredHint::Opaque,
                Some(Hint::Abbrev) => StoredHint::Abbrev,
                Some(Hint::Regular(_)) => StoredHint::Regular(hint_span),
            },
        };
        self.by_name.resize(index_end, 0);
        self.no_rule
            .resize_with(index_end.div_ceil(64), Default::default);
        self.names.extend_from_slice(request.parameters);
        self.names.extend_from_slice(request.all);
        self.hints.extend_from_slice(bytes);
        self.entries.push(entry);
        self.by_name[key] = encoded;
        Ok(())
    }
    fn check_visibility(
        &self,
        before: usize,
        formation: Option<Formation>,
    ) -> Result<(), ResourceError> {
        match formation {
            None if before <= self.len() => Ok(()),
            Some(phase)
                if self.stage.is_some_and(|s| s.phase == phase)
                    && before == phase.before()
                    && before == self.entries.len() =>
            {
                Ok(())
            }
            _ => Err(ResourceError::Invariant),
        }
    }
    pub(crate) fn check_scope(
        &self,
        before: usize,
        formation: Option<Formation>,
        expression_end: usize,
        level_end: usize,
    ) -> Result<(), ResourceError> {
        self.check_visibility(before, formation)?;
        if let Some(phase) = formation {
            let stage = self.stage.ok_or(ResourceError::Invariant)?;
            if stage.phase != phase
                || stage.expression_end as usize != expression_end
                || stage.level_end as usize != level_end
            {
                return Err(ResourceError::Invariant);
            }
        } else if before != self.len() {
            return Err(ResourceError::Invariant);
        }
        Ok(())
    }
    fn next_phase(&mut self, before: usize) -> Result<Formation, ResourceError> {
        let epoch = self
            .epoch
            .checked_add(1)
            .and_then(NonZeroU32::new)
            .ok_or(ResourceError::Counter)?;
        let before = u32::try_from(before).map_err(|_| ResourceError::Counter)?;
        self.epoch = epoch.get();
        Ok(Formation { epoch, before })
    }
    fn begin_stage(
        &mut self,
        expression_end: usize,
        level_end: usize,
        b: &mut Budget,
    ) -> Result<Formation, ResourceError> {
        b.charge_work(1)?;
        if self.stage.is_some() || self.entries.len() != self.len() {
            return Err(ResourceError::Invariant);
        }
        let expression_end = u32::try_from(expression_end).map_err(|_| ResourceError::Counter)?;
        let level_end = u32::try_from(level_end).map_err(|_| ResourceError::Counter)?;
        let phase = self.next_phase(self.entries.len())?;
        self.stage = Some(Stage {
            phase,
            expression_end,
            level_end,
            auxiliary: None,
        });
        Ok(phase)
    }
    /// The nested owner has frozen its own template pool. It must keep that pool
    /// and names alive, and check every signature before stage_signature. This
    /// capability grants typing only; imported scope bounds stay unchanged.
    fn begin_auxiliary_stage(
        &mut self,
        expression_end: usize,
        level_end: usize,
        expressions: &crate::syntax::expressions::Expressions,
        levels: &crate::syntax::levels::Levels,
        b: &mut Budget,
    ) -> Result<Formation, ResourceError> {
        if expression_end > expressions.len() || level_end > levels.len() {
            return Err(ResourceError::Invariant);
        }
        let templates = AuxiliaryTemplates {
            expression_end: u32::try_from(expressions.len()).map_err(|_| ResourceError::Counter)?,
            level_end: u32::try_from(levels.len())
                .ok()
                .and_then(NonZeroU32::new)
                .ok_or(ResourceError::Invariant)?,
        };
        let phase = self.begin_stage(expression_end, level_end, b)?;
        self.stage
            .as_mut()
            .ok_or(ResourceError::Invariant)?
            .auxiliary = Some(templates);
        Ok(phase)
    }
    fn require_public_stage(&self) -> Result<(), ResourceError> {
        if self
            .stage
            .ok_or(ResourceError::Invariant)?
            .auxiliary
            .is_some()
        {
            Err(ResourceError::Invariant)
        } else {
            Ok(())
        }
    }

    fn stage_signature(
        &mut self,
        phase: Formation,
        signature: SignatureInput<'_>,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Formation, ResourceError> {
        self.check_visibility(phase.before(), Some(phase))?;
        let old = self.stage.ok_or(ResourceError::Invariant)?;
        // Invalidate the supplied phase before fallible work. An interrupted
        // append cannot be resumed using a previously exposed formation scope.
        let mut next = self.next_phase(self.entries.len())?;
        self.stage = Some(Stage { phase: next, ..old });
        b.charge_work(1)?;
        let (end, ty) = match old.auxiliary {
            Some(templates) => (
                templates.expression_end,
                TypeSource::Auxiliary(signature.ty.slot()),
            ),
            None => (old.expression_end, TypeSource::Original(signature.ty)),
        };
        if signature.ty.slot() >= end {
            return Err(ResourceError::Invariant);
        }
        self.append_entry(
            &ConstantSignature {
                slot: None,
                kind: StoredKind::Signature(signature.kind),
                name: signature.name,
                parameters: signature.parameters,
                ty,
                value: None,
                all: signature.all,
                safety: Safety::Safe,
                hint: None,
            },
            names,
            b,
        )?;
        next.before = u32::try_from(self.entries.len()).map_err(|_| ResourceError::Counter)?;
        self.stage = Some(Stage { phase: next, ..old });
        Ok(next)
    }
    fn signature_stage_checkpoint(&self) -> Result<SignatureStageCheckpoint, ResourceError> {
        if self.stage.is_some() || self.entries.len() != self.len() {
            return Err(ResourceError::Invariant);
        }
        Ok(SignatureStageCheckpoint {
            metadata: [
                self.constructors.len(),
                self.recursors.len(),
                self.families.len(),
                self.rules.len(),
            ],
            committed: self.committed,
            epoch: self.epoch,
        })
    }

    /// Retire an original or auxiliary signature stage without publication.
    /// Imported and auxiliary template bounds stay distinct; retirement grants
    /// neither generated-root authority nor admission. The outer nested owner
    /// retires any remaining stage before syntax rollback.
    /// Capacities remain owned and charged until Environment::retire.
    fn retire_signature_stage(
        &mut self,
        checkpoint: SignatureStageCheckpoint,
        phase: Formation,
        names: &Names,
        b: &mut Budget,
    ) -> Result<(), ResourceError> {
        self.check_visibility(phase.before(), Some(phase))?;
        let old = self.stage.ok_or(ResourceError::Invariant)?;
        // Even interrupted retirement invalidates every previously issued token.
        let next = self.next_phase(self.entries.len())?;
        self.stage = Some(Stage { phase: next, ..old });
        let committed = self.len();
        b.charge_work((self.entries.len() - committed) as u64 + 1)?;
        // This primitive cannot erase an unsafe candidate or prepared computation
        // metadata. Those owners have different publication/rollback obligations.
        if self.entries[committed..].iter().any(|entry| {
            !matches!(entry.kind, StoredKind::Signature(_))
                || entry.value.is_some()
                || !matches!(entry.hint, StoredHint::None)
        }) || checkpoint.committed != self.committed
            || checkpoint.epoch >= phase.epoch.get()
            || checkpoint.metadata
                != [
                    self.constructors.len(),
                    self.recursors.len(),
                    self.families.len(),
                    self.rules.len(),
                ]
        {
            return Err(ResourceError::Invariant);
        }
        let name_end = self
            .entries
            .get(committed)
            .map_or(self.names.len(), |entry| entry.parameters.offset as usize);
        for (offset, entry) in self.entries[committed..].iter().enumerate() {
            let key = names.summary(entry.name, b)?.canonical as usize;
            let slot = self.by_name.get_mut(key).ok_or(ResourceError::Invariant)?;
            if *slot as usize != committed + offset + 1 {
                return Err(ResourceError::Invariant);
            }
            *slot = 0;
        }
        self.entries.truncate(committed);
        self.names.truncate(name_end);
        self.stage = None;
        Ok(())
    }
}
fn span(offset: usize, len: usize) -> Result<Span, ResourceError> {
    let end = offset.checked_add(len).ok_or(ResourceError::Counter)?;
    crate::resource::traced!("environment.slot_limit", end, {
        u32::try_from(end).map_err(|_| ResourceError::Storage)
    })?;
    Ok(Span {
        offset: offset as u32,
        len: len as u32,
    })
}
fn view<T>(store: &[T], span: Span) -> Result<&[T], ResourceError> {
    store
        .get(span.offset as usize..span.offset as usize + span.len as usize)
        .ok_or(ResourceError::Invariant)
}
