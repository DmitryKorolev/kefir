//! Fixed, owned failure evidence for test and introspection builds.
//! Captures are read-only and uncharged. They grant no semantic judgment and
//! never participate in outcome or reason-code selection.
use crate::check::delayed::environment::{EnvId, Environment};
use crate::check::diagnostic::{self, Limits, Sources};
use crate::syntax::expressions::ExprId;
use crate::syntax::levels::{LevelId, NameId};
use crate::syntax::local_context::LocalContext;
use std::mem::size_of;

const NAME_BYTES: usize = 1_024;
const RULES: usize = 12;
const IDENTITIES: usize = 16;
const VALUES: usize = 8;
const BINDINGS: usize = 32;
const LOCALS: usize = 32;
const TERMS: usize = 2;
const TERM_BYTES: usize = 256;
const TERM_DEPTH: u32 = 32;
const TERM_NODES: u16 = 128;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum Rule {
    Setup,
    Decode,
    DeclarationPolicy,
    QuotientValidation,
    ConstructorValidation,
    Positivity,
    Formation,
    Inference,
    Conversion,
    UnsupportedReduction,
    ExportMatch,
    Publication,
    Cleanup,
}
impl Rule {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Setup => "checking setup",
            Self::Decode => "decode",
            Self::DeclarationPolicy => "declaration policy",
            Self::QuotientValidation => "quotient validation",
            Self::ConstructorValidation => "constructor validation",
            Self::Positivity => "positivity",
            Self::Formation => "formation",
            Self::Inference => "inference",
            Self::Conversion => "conversion rule",
            Self::UnsupportedReduction => "unsupported reduction",
            Self::ExportMatch => "export mismatch",
            Self::Publication => "publication",
            Self::Cleanup => "cleanup",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum Role {
    Declaration,
    Root,
    Expected,
    Actual,
    Type,
    Value,
    Binder,
    Universe,
    Environment,
    Local,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Identity {
    Expression { role: Role, slot: u32 },
    Level { role: Role, slot: u32 },
    Name { role: Role, slot: u32 },
    Environment { role: Role, slot: u32 },
    Local { role: Role, slot: u32 },
}
impl Identity {
    pub(crate) fn expression(role: Role, id: ExprId) -> Self {
        Self::Expression {
            role,
            slot: id.slot(),
        }
    }

    pub(crate) fn level(role: Role, id: LevelId) -> Self {
        Self::Level {
            role,
            slot: id.slot(),
        }
    }

    pub(crate) fn name(role: Role, id: NameId) -> Self {
        Self::Name { role, slot: id.0 }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum Invariant {
    Unavailable,
    ImportedSlot,
    DeclarationSequence,
    CheckedScope,
    LocalContext,
    GeneratedFrontier,
    EnvironmentPublication,
    StoredSyntax,
    StreamState,
    Cleanup,
}
impl Invariant {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Unavailable => "internal invariant unavailable at capture boundary",
            Self::ImportedSlot => "imported slot matches physical slot",
            Self::DeclarationSequence => "declaration ordinal follows checked prefix",
            Self::CheckedScope => "checked scope matches session origins",
            Self::LocalContext => "local context is balanced",
            Self::GeneratedFrontier => "generated syntax stays beyond its frontier",
            Self::EnvironmentPublication => "validated environment publication is atomic",
            Self::StoredSyntax => "stored syntax satisfies construction validation",
            Self::StreamState => "stream state follows one terminal sequence",
            Self::Cleanup => "failure cleanup retires all owned state",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum ValueRole {
    Expected,
    Actual,
    Start,
    End,
    Length,
    Index,
    Depth,
    Ordinal,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Value {
    pub role: ValueRole,
    pub value: u64,
}

#[derive(Clone, Copy)]
pub(crate) struct InvariantEvidence<'a> {
    pub invariant: Invariant,
    pub values: &'a [Value],
}

#[derive(Clone, Copy)]
pub(crate) struct Delayed<'a> {
    pub expression: ExprId,
    pub environment: EnvId,
    pub environments: &'a Environment,
    pub locals: &'a LocalContext,
}

/// The two checked types a failed conversion compared, in the caller's
/// expected/actual orientation. Evidence only; it grants no semantic judgment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Mismatch {
    pub expected: ExprId,
    pub actual: ExprId,
}

/// One bounded rendered term owned by the snapshot. Fixed capacity keeps
/// capture allocation-free; the text is the diagnostic renderer's own output.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Term {
    pub role: Role,
    pub slot: u32,
    text: [u8; TERM_BYTES],
    len: u16,
}
impl Term {}

#[derive(Clone, Copy)]
pub(crate) struct Capture<'a> {
    pub declaration: Option<NameId>,
    pub rules: &'a [Rule],
    pub identities: &'a [Identity],
    pub invariant: Option<InvariantEvidence<'a>>,
    pub delayed: Option<Delayed<'a>>,
    pub mismatch: Option<Mismatch>,
    pub sources: Sources<'a>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Truncated {
    pub declaration: bool,
    pub rules: bool,
    pub identities: bool,
    pub invariant_values: bool,
    pub environment: bool,
    pub locals: bool,
    pub delayed_context: bool,
    pub terms: bool,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct Local {
    pub id: u32,
    pub active: bool,
    pub name: u32,
    pub ty: u32,
    pub value: Option<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Snapshot {
    declaration: [u8; NAME_BYTES],
    declaration_len: u16,
    rules: [Option<Rule>; RULES],
    rules_len: u8,
    identities: [Option<Identity>; IDENTITIES],
    identities_len: u8,
    invariant: Option<Invariant>,
    values: [Option<Value>; VALUES],
    values_len: u8,
    delayed_expression: Option<u32>,
    delayed_environment: Option<u32>,
    bindings: [u32; BINDINGS],
    bindings_len: u8,
    locals: [Local; LOCALS],
    locals_len: u8,
    terms: [Term; TERMS],
    terms_len: u8,
    mismatch: Option<(u32, u32)>,
    truncated: Truncated,
}
const _: () = assert!(size_of::<Snapshot>() == 2_768);

impl Snapshot {
    fn empty() -> Self {
        Self {
            declaration: [0; NAME_BYTES],
            declaration_len: 0,
            rules: [None; RULES],
            rules_len: 0,
            identities: [None; IDENTITIES],
            identities_len: 0,
            invariant: None,
            values: [None; VALUES],
            values_len: 0,
            delayed_expression: None,
            delayed_environment: None,
            bindings: [0; BINDINGS],
            bindings_len: 0,
            locals: [Local::default(); LOCALS],
            locals_len: 0,
            terms: [Term {
                role: Role::Declaration,
                slot: 0,
                text: [0; TERM_BYTES],
                len: 0,
            }; TERMS],
            terms_len: 0,
            mismatch: None,
            truncated: Truncated::default(),
        }
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn rule_invariant(rule: Rule, invariant: Option<Invariant>) -> Self {
        let mut snapshot = Self::empty();
        snapshot.rules[0] = Some(rule);
        snapshot.rules_len = 1;
        snapshot.invariant = invariant;
        snapshot
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn unavailable_delayed_context() -> Self {
        let mut snapshot = Self::empty();
        snapshot.truncated.delayed_context = true;
        snapshot
    }

    pub(crate) fn capture(input: Capture<'_>) -> Self {
        let mut snapshot = Self::empty();
        snapshot.invariant = input.invariant.map(|evidence| evidence.invariant);
        if let Some(name) = input.declaration {
            let rendered = diagnostic::name(
                name,
                input.sources,
                Limits::new(64, 1, NAME_BYTES as u16).expect("fixed diagnostic limits"),
            );
            let bytes = rendered.as_bytes();
            let len = bytes.len().min(NAME_BYTES);
            snapshot.declaration[..len].copy_from_slice(&bytes[..len]);
            snapshot.declaration_len = len as u16;
            snapshot.truncated.declaration = rendered.truncation() != Default::default();
        }
        snapshot.rules_len = input.rules.len().min(RULES) as u8;
        for (target, rule) in snapshot.rules.iter_mut().zip(input.rules.iter().copied()) {
            *target = Some(rule);
        }
        snapshot.truncated.rules = input.rules.len() > RULES;
        snapshot.identities_len = input.identities.len().min(IDENTITIES) as u8;
        for (target, identity) in snapshot
            .identities
            .iter_mut()
            .zip(input.identities.iter().copied())
        {
            *target = Some(identity);
        }
        snapshot.truncated.identities = input.identities.len() > IDENTITIES;
        if let Some(evidence) = input.invariant {
            snapshot.values_len = evidence.values.len().min(VALUES) as u8;
            for (target, value) in snapshot
                .values
                .iter_mut()
                .zip(evidence.values.iter().copied())
            {
                *target = Some(value);
            }
            snapshot.truncated.invariant_values = evidence.values.len() > VALUES;
        }
        if let Some(mismatch) = input.mismatch {
            // Rendered terms are bounded, stack-rendered evidence: the renderer
            // is read-only and charges no semantic work, so capture stays
            // allocation-free and budget-neutral.
            let limits = Limits::new(TERM_DEPTH, TERM_NODES, TERM_BYTES as u16)
                .expect("fixed diagnostic limits");
            let (expected, expected_cut) =
                rendered_term(Role::Expected, mismatch.expected, input.sources, limits);
            snapshot.terms[0] = expected;
            let (actual, actual_cut) =
                rendered_term(Role::Actual, mismatch.actual, input.sources, limits);
            snapshot.terms[1] = actual;
            snapshot.terms_len = TERMS as u8;
            snapshot.mismatch = Some((mismatch.expected.slot(), mismatch.actual.slot()));
            snapshot.truncated.terms = expected_cut || actual_cut;
        }
        if let Some(delayed) = input.delayed {
            snapshot.delayed_expression = Some(delayed.expression.slot());
            snapshot.delayed_environment = Some(delayed.environment.diagnostic_slot());
            let length = match delayed.environments.diagnostic_len(delayed.environment) {
                Ok(length) => length,
                Err(_) => {
                    snapshot.truncated.environment = true;
                    0
                }
            };
            let retained = usize::try_from(length).unwrap_or(usize::MAX).min(BINDINGS);
            for index in 0..retained {
                match delayed
                    .environments
                    .diagnostic_lookup(delayed.environment, index as u32)
                {
                    Ok(binding) => snapshot.bindings[index] = binding.slot(),
                    Err(_) => {
                        snapshot.truncated.environment = true;
                        break;
                    }
                }
                snapshot.bindings_len += 1;
            }
            snapshot.truncated.environment |=
                usize::try_from(length).unwrap_or(usize::MAX) > retained;
            let local_len = delayed.locals.diagnostic_len();
            let retained = local_len.min(LOCALS);
            for id in 0..retained {
                let Some((local, active)) = delayed.locals.diagnostic_get(id as u32) else {
                    snapshot.truncated.locals = true;
                    break;
                };
                snapshot.locals[id] = Local {
                    id: id as u32,
                    active,
                    name: local.name().0,
                    ty: local.ty().slot(),
                    value: local.value().map(ExprId::slot),
                };
                snapshot.locals_len += 1;
            }
            snapshot.truncated.locals |= local_len > retained;
        }
        snapshot
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn merge_context(&mut self, context: &Self) {
        if self.delayed_expression.is_none() {
            self.delayed_expression = context.delayed_expression;
            self.delayed_environment = context.delayed_environment;
            self.bindings = context.bindings;
            self.bindings_len = context.bindings_len;
            self.locals = context.locals;
            self.locals_len = context.locals_len;
            self.truncated.environment |= context.truncated.environment;
            self.truncated.locals |= context.truncated.locals;
            self.truncated.delayed_context |= context.truncated.delayed_context;
        }
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn has_rules(&self) -> bool {
        self.rules_len != 0
    }

    #[cfg(feature = "introspection")]
    pub(crate) fn ensure_invariant(&mut self, invariant: Invariant) {
        if self.invariant.is_none() {
            self.invariant = Some(invariant);
        }
    }

    pub(crate) fn declaration(&self) -> &[u8] {
        &self.declaration[..usize::from(self.declaration_len)]
    }

    pub(crate) fn rules(&self) -> impl Iterator<Item = Rule> + '_ {
        self.rules[..usize::from(self.rules_len)]
            .iter()
            .flatten()
            .copied()
    }

    pub(crate) fn identities(&self) -> impl Iterator<Item = Identity> + '_ {
        self.identities[..usize::from(self.identities_len)]
            .iter()
            .flatten()
            .copied()
    }

    pub(crate) fn invariant(&self) -> Option<(Invariant, impl Iterator<Item = Value> + '_)> {
        self.invariant.map(|invariant| {
            (
                invariant,
                self.values[..usize::from(self.values_len)]
                    .iter()
                    .flatten()
                    .copied(),
            )
        })
    }

    pub(crate) fn delayed(&self) -> Option<(u32, u32, &[u32], &[Local])> {
        Some((
            self.delayed_expression?,
            self.delayed_environment?,
            &self.bindings[..usize::from(self.bindings_len)],
            &self.locals[..usize::from(self.locals_len)],
        ))
    }

    pub(crate) fn terms(&self) -> impl Iterator<Item = &Term> + '_ {
        self.terms[..usize::from(self.terms_len)].iter()
    }

    pub(crate) fn mismatch(&self) -> Option<(&Term, &Term)> {
        let (expected, actual) = self.mismatch?;
        Some((
            self.terms()
                .find(|term| term.role == Role::Expected && term.slot == expected)?,
            self.terms()
                .find(|term| term.role == Role::Actual && term.slot == actual)?,
        ))
    }

    pub(crate) fn truncation(&self) -> Truncated {
        self.truncated
    }
}

fn rendered_term(
    role: Role,
    expression: ExprId,
    sources: Sources<'_>,
    limits: Limits,
) -> (Term, bool) {
    let rendered = diagnostic::term(expression, sources, limits);
    let mut term = Term {
        role,
        slot: expression.slot(),
        text: [0; TERM_BYTES],
        len: 0,
    };
    let bytes = rendered.as_bytes();
    let len = bytes.len().min(TERM_BYTES);
    term.text[..len].copy_from_slice(&bytes[..len]);
    term.len = len as u16;
    (term, rendered.truncation() != Default::default())
}

// Capture hooks and the rendered-term follow-up consume this interface. Keep it
// type-checked in an introspection library before every failure class is wired.
#[cfg(feature = "introspection")]
const _: () = {
    let _ = [
        Rule::Setup,
        Rule::Decode,
        Rule::DeclarationPolicy,
        Rule::QuotientValidation,
        Rule::ConstructorValidation,
        Rule::Positivity,
        Rule::Formation,
        Rule::Inference,
        Rule::Conversion,
        Rule::UnsupportedReduction,
        Rule::ExportMatch,
        Rule::Publication,
        Rule::Cleanup,
    ];
    let _ = Rule::name;
    let _ = [
        Role::Declaration,
        Role::Root,
        Role::Expected,
        Role::Actual,
        Role::Type,
        Role::Value,
        Role::Binder,
        Role::Universe,
        Role::Environment,
        Role::Local,
    ];
    let _ = Identity::Environment {
        role: Role::Environment,
        slot: 0,
    };
    let _ = Identity::Local {
        role: Role::Local,
        slot: 0,
    };
    let _ = Identity::expression;
    let _ = Identity::level;
    let _ = Identity::name;
    let _ = Invariant::name;
    let _ = [
        Invariant::Unavailable,
        Invariant::ImportedSlot,
        Invariant::DeclarationSequence,
        Invariant::CheckedScope,
        Invariant::LocalContext,
        Invariant::GeneratedFrontier,
        Invariant::EnvironmentPublication,
        Invariant::StoredSyntax,
        Invariant::StreamState,
        Invariant::Cleanup,
    ];
    let _ = [
        ValueRole::Expected,
        ValueRole::Actual,
        ValueRole::Start,
        ValueRole::End,
        ValueRole::Length,
        ValueRole::Index,
        ValueRole::Depth,
        ValueRole::Ordinal,
    ];
    let _ = Snapshot::capture;
    let _ = Snapshot::declaration;
    let _ = Snapshot::rules;
    let _ = Snapshot::identities;
    let _ = Snapshot::invariant;
    let _ = Snapshot::delayed;
    let _ = Snapshot::terms;
    let _ = Snapshot::mismatch;
    let _ = Snapshot::truncation;
    #[cfg(feature = "introspection")]
    let _ = crate::resource::Budget::failure_snapshot;
};
