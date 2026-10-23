//! Ordinary constant type transport and immediate delta. Does not validate entries.
use super::*;
use crate::resource::{Event, ReductionPath};
use crate::syntax::expressions::{ExpressionError, Expressions};
use crate::syntax::levels::{Instance, LevelId, Levels, ScopeError};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Mode {
    Safe,
    Unsafe,
}
/// The validator fixes these frontiers and the caller's universe scope. They
/// must originate in this run; generated templates are not admitted by supplying
/// a later numeric frontier. Formation requires its live validator-minted token.
pub(crate) struct ConstantUse<'a> {
    pub name: NameId,
    pub arguments: &'a [LevelId],
    pub parameters: &'a [NameId],
    pub before: usize,
    pub formation: Option<Formation>,
    pub mode: Mode,
    pub expression_end: usize,
    pub level_end: usize,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum UseError {
    Resource(ResourceError),
    Unavailable,
    UnsafeUse,
    Arity,
    /// Exact arithmetic authority and two checked closed literals were
    /// established, but their computation exceeds implemented backend bounds.
    LiteralArithmetic,
    Scope(ScopeError),
    Expression(ExpressionError),
}
impl From<ResourceError> for UseError {
    fn from(e: ResourceError) -> Self {
        Self::Resource(e)
    }
}
impl From<ScopeError> for UseError {
    fn from(e: ScopeError) -> Self {
        match e {
            ScopeError::Resource(e) => Self::Resource(e),
            e => Self::Scope(e),
        }
    }
}
impl From<ExpressionError> for UseError {
    fn from(e: ExpressionError) -> Self {
        match e {
            ExpressionError::Resource(e) => Self::Resource(e),
            e => Self::Expression(e),
        }
    }
}
/// Borrowed installed-definition classification, not transported syntax or a
/// checking certificate. Used only to schedule permitted comparison routes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DeltaCandidate {
    pub priority: (u8, u32),
    pub body: ExprId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DeltaStep {
    Unfolded {
        expression: ExprId,
        path: ReductionPath,
    },
    /// No ordinary delta body, including signature-only staged constants.
    /// This grants no iota/projection/K computation or normal-form certificate.
    NoDelta,
    /// A recursor requires its own completed reduction route. This is never a
    /// rigid-head certificate, including in private signature-only phases.
    Recursor,
    /// Validated quotient eliminator requires its own completed reduction route.
    Quotient(QuotientRole),
}
impl Environment {
    /// The evaluator selected this rule from committed, independently checked
    /// nullary metadata. Transport only its original matched RHS; generated
    /// staging roots and signatures without computation authority are excluded.
    #[allow(clippy::too_many_arguments)] // Existing syntax stores plus scoped optional transport cache.
    pub(crate) fn instantiate_nullary_rule_with_cache(
        &self,
        use_site: ConstantUse<'_>,
        index: usize,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        mut cache: Option<(
            &mut instantiation::Cache,
            &mut crate::resource::SessionCacheBudget,
        )>,
        b: &mut Budget,
    ) -> Result<ExprId, UseError> {
        let entry = self.check_use(&use_site, levels, names, b)?;
        if entry.kind != StoredKind::Signature(SignatureKind::Recursor) {
            return Err(ResourceError::Invariant.into());
        }
        let recursor = self
            .recursor(use_site.name, use_site.before.min(self.len()), names, b)?
            .ok_or(UseError::Unavailable)?;
        let rhs = recursor
            .rules
            .get(index)
            .ok_or(ResourceError::Invariant)?
            .rhs;
        if use_site.formation.is_some() || entry.parameters.is_empty() {
            cache = None;
        }
        if cache.is_some()
            && (rhs.slot() as usize >= use_site.expression_end
                || use_site.expression_end > expressions.len()
                || use_site.level_end > levels.len())
        {
            return Err(ResourceError::Invariant.into());
        }
        let rule = u32::try_from(index).map_err(|_| ResourceError::Counter)?;
        if let Some((table, _)) = cache.as_mut()
            && let Some(result) = table.get_rule(
                entry.slot.ok_or(ResourceError::Invariant)?,
                rule,
                use_site.arguments,
                expressions,
                b,
            )?
        {
            return Ok(result);
        }
        let result = expressions.with_universe_substitution(
            levels,
            names,
            Instance {
                expression_end: use_site.expression_end,
                level_end: use_site.level_end,
                parameters: entry.parameters,
                replacements: use_site.arguments,
            },
            b,
            |substitution| substitution.apply(rhs),
        )?;
        // Only completed original syntax transport, including scratch retirement.
        // Iota and all ordinary RHS beta steps are charged by the evaluator.
        if let Some((table, session)) = cache {
            table.insert_rule(
                entry.slot.ok_or(ResourceError::Invariant)?,
                rule,
                use_site.arguments,
                result,
                session,
                b,
            )?;
        }
        Ok(result)
    }
    /// Requires the environment's validated-entry invariant. Storage-only tests
    /// bypass validation deliberately; production installation is validator-owned.
    /// Check prior visibility, safety, exact arity and argument scope BEFORE
    /// substituting the original type. Supplied level handles are preserved by
    /// The frozen-template transport; no body is inspected or unfolded.
    /// No checkedness/cache entry is returned on failure. Generated partial
    /// syntax on failure belongs to the caller's declaration watermark and must
    /// be reclaimed or discarded with the run. The positive-only slice declines
    /// failed premises; these errors do not authorize a negative proof verdict.
    pub(crate) fn instantiate_type(
        &self,
        use_site: ConstantUse<'_>,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<ExprId, UseError> {
        let entry = self.check_use(&use_site, levels, names, b)?;
        if let TypeSource::Quotient(role) = entry.ty {
            let package = self.quotient.as_ref().ok_or(ResourceError::Invariant)?;
            return Ok(quotient::schema::build(
                role,
                &package.names,
                use_site.arguments,
                expressions,
                levels,
                names,
                b,
            )?);
        }
        if let TypeSource::Auxiliary(slot) = entry.ty {
            // check_use established the current phase and original scope bounds.
            // Only lookup of that phase's private signature can return Auxiliary.
            // Its immutable template pool outlives all inner checking sessions.
            let templates = self
                .stage
                .and_then(|stage| stage.auxiliary)
                .ok_or(ResourceError::Invariant)?;
            if templates.expression_end as usize > expressions.len()
                || templates.level_end.get() as usize > levels.len()
                || slot >= templates.expression_end
            {
                return Err(ResourceError::Invariant.into());
            }
            let ty = expressions.resolve_slot(slot, b)?;
            return Ok(expressions.with_uncached_universe_substitution(
                levels,
                names,
                Instance {
                    expression_end: templates.expression_end as usize,
                    level_end: templates.level_end.get() as usize,
                    parameters: entry.parameters,
                    replacements: use_site.arguments,
                },
                b,
                |substitution| substitution.apply(ty),
            )?);
        }
        let TypeSource::Original(ty) = entry.ty else {
            return Err(ResourceError::Invariant.into());
        };
        if use_site.formation.is_none() {
            b.charge_work(1)?;
            if use_site.expression_end > expressions.len()
                || use_site.level_end > levels.len()
                || ty.slot() as usize >= use_site.expression_end
            {
                return Err(ResourceError::Invariant.into());
            }
            // Installed entries have valid, canonically unique parameters by
            // validation. check_use above still checks every supplied argument,
            // including unused ones. The immutable summary proves transport
            // identity; no generated/formation template enters this shortcut.
            if !expressions.get(ty, b)?.has_param() {
                return Ok(ty);
            }
        }
        let result = expressions.with_universe_substitution(
            levels,
            names,
            Instance {
                expression_end: use_site.expression_end,
                level_end: use_site.level_end,
                parameters: entry.parameters,
                replacements: use_site.arguments,
            },
            b,
            |substitution| substitution.apply(ty),
        )?;
        Ok(result)
    }
    // Shared preconditions do not establish typing: entries must already satisfy
    // the owning validator's invariant, and generated frontiers cannot be forged.
    pub(super) fn check_use<'a>(
        &'a self,
        use_site: &ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<ConstantSignature<'a>, UseError> {
        b.charge_work(1)?;
        if use_site.formation.is_some() {
            self.check_scope(
                use_site.before,
                use_site.formation,
                use_site.expression_end,
                use_site.level_end,
            )?;
        }
        let entry = self
            .lookup_visible(use_site.name, use_site.before, use_site.formation, names, b)?
            .ok_or(UseError::Unavailable)?;
        if use_site.mode == Mode::Safe && entry.safety != Safety::Safe {
            return Err(UseError::UnsafeUse);
        }
        if entry.parameters.len() != use_site.arguments.len() {
            return Err(UseError::Arity);
        }
        levels.check_scope(names, use_site.parameters, use_site.arguments, b)?;
        Ok(entry)
    }

    /// Classification for the bounded ordered-congruence route. A signature
    /// role grants no computation; callers separately exclude intrinsic names.
    pub(crate) fn inductive_type_use(
        &self,
        site: ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<bool, UseError> {
        Ok(self.check_use(&site, levels, names, b)?.kind
            == StoredKind::Signature(SignatureKind::Inductive))
    }

    /// A validated rigid head has no ordinary delta body. Primitive-name
    /// applicability is a separate caller guard; declaration kind alone cannot
    /// dismiss intrinsic operations. No reduction or equality follows here.
    pub(crate) fn rigid_constant_use(
        &self,
        site: ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<bool, UseError> {
        Ok(matches!(
            self.check_use(&site, levels, names, b)?.kind,
            StoredKind::Ordinary(Kind::Axiom | Kind::Opaque)
                | StoredKind::Signature(SignatureKind::Inductive)
        ))
    }

    /// A validated axiom or opaque constant: no ordinary delta body, so an
    /// application of it is a stuck value. Primitive-name applicability is a
    /// separate caller guard. No reduction or equality follows here.
    pub(crate) fn stuck_value_use(
        &self,
        site: ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<bool, UseError> {
        Ok(matches!(
            self.check_use(&site, levels, names, b)?.kind,
            StoredKind::Ordinary(Kind::Axiom | Kind::Opaque)
        ))
    }

    /// Role of a validated committed quotient primitive use, or None for any other
    /// entry. Validation is the same scope, safety and arity check as every use;
    /// this grants no reduction and no equality by itself.
    pub(crate) fn quotient_role_use(
        &self,
        site: ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Option<QuotientRole>, UseError> {
        Ok(match self.check_use(&site, levels, names, b)?.kind {
            StoredKind::Quotient(role) => Some(role),
            _ => None,
        })
    }

    /// A validated use of committed `Quot`, `Quot.mk` or a recursor: heads that have no
    /// ordinary delta body. Same-name uses with completed-equal universe instances are
    /// the same term (committed head equality); this grants no reduction.
    pub(crate) fn opaque_head_use(
        &self,
        site: ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<bool, UseError> {
        Ok(matches!(
            self.check_use(&site, levels, names, b)?.kind,
            StoredKind::Quotient(QuotientRole::Type | QuotientRole::Constructor)
                | StoredKind::Signature(SignatureKind::Recursor)
        ))
    }

    /// Restricted exposure classifies validated uses without transporting a body.
    /// NoDelta means no rule in this mode, not global head normality.
    pub(crate) fn restricted_head_step(
        &self,
        use_site: ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<DeltaStep, UseError> {
        let entry = self.check_use(&use_site, levels, names, b)?;
        Ok(match entry.kind {
            StoredKind::Signature(SignatureKind::Recursor) => DeltaStep::Recursor,
            StoredKind::Quotient(role @ (QuotientRole::Lift | QuotientRole::Induction)) => {
                DeltaStep::Quotient(role)
            }
            _ => DeltaStep::NoDelta,
        })
    }

    /// Inspect a validated candidate without transporting its body or charging a
    /// reduction. None establishes only ordinary delta inapplicability. Failed
    /// visibility, safety, arity, scope, or a promised missing body stays an error.
    pub(crate) fn delta_candidate(
        &self,
        site: ConstantUse<'_>,
        levels: &Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<Option<DeltaCandidate>, UseError> {
        let entry = self.check_use(&site, levels, names, b)?;
        let hint = match entry.kind {
            StoredKind::Ordinary(Kind::Definition) => entry.hint.ok_or(ResourceError::Invariant)?,
            StoredKind::Ordinary(Kind::Theorem) => Hint::Opaque,
            _ => return Ok(None),
        };
        let body = entry.value.ok_or(ResourceError::Invariant)?;
        let priority = match hint {
            Hint::Abbrev => (2, 0),
            Hint::Opaque => (0, 0),
            Hint::Regular(bytes) => {
                // Exact exported UInt32 priority; no recomputation from the body.
                b.charge_work(bytes.len() as u64 + 1)?;
                let mut height = 0u32;
                for &digit in bytes {
                    if !digit.is_ascii_digit() {
                        return Err(ResourceError::Invariant.into());
                    }
                    height = height
                        .checked_mul(10)
                        .and_then(|n| n.checked_add((digit - b'0') as u32))
                        .ok_or(UseError::Unavailable)?;
                }
                (1, height)
            }
        };
        Ok(Some(DeltaCandidate { priority, body }))
    }

    /// Ordinary installed-definition/theorem rule. Caller chooses
    /// when delta is permitted; this primitive does not implement paired order,
    /// head exposure or normal-form certification. Candidate access uses
    /// the same live-phase and unsafe-mode checks as type transport.
    /// Partial generated syntax is declaration-watermark owned on every error.
    pub(crate) fn delta_step(
        &self,
        use_site: ConstantUse<'_>,
        path: ReductionPath,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        b: &mut Budget,
    ) -> Result<DeltaStep, UseError> {
        self.delta_step_with_cache(use_site, path, expressions, levels, names, None, b)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn delta_step_with_cache(
        &self,
        use_site: ConstantUse<'_>,
        path: ReductionPath,
        expressions: &mut Expressions,
        levels: &mut Levels,
        names: &Names,
        mut cache: Option<(
            &mut instantiation::Cache,
            &mut crate::resource::SessionCacheBudget,
        )>,
        b: &mut Budget,
    ) -> Result<DeltaStep, UseError> {
        let entry = self.check_use(&use_site, levels, names, b)?;
        match entry.kind {
            StoredKind::Signature(SignatureKind::Recursor) => return Ok(DeltaStep::Recursor),
            StoredKind::Quotient(QuotientRole::Type | QuotientRole::Constructor) => {
                return Ok(DeltaStep::NoDelta);
            }
            StoredKind::Quotient(role) => return Ok(DeltaStep::Quotient(role)),
            StoredKind::Ordinary(Kind::Axiom | Kind::Opaque) | StoredKind::Signature(_) => {
                return Ok(DeltaStep::NoDelta);
            }
            StoredKind::Ordinary(Kind::Definition | Kind::Theorem) => {}
        }
        let body = entry.value.ok_or(ResourceError::Invariant)?;
        let next = path.after_reduction()?;
        // The driver fixes the full session. Formation and parameter-free bodies
        // deliberately retain the uncached construction path.
        if use_site.formation.is_some() || entry.parameters.is_empty() {
            cache = None;
        }
        if cache.is_some()
            && (body.slot() as usize >= use_site.expression_end
                || use_site.expression_end > expressions.len()
                || use_site.level_end > levels.len())
        {
            return Err(ResourceError::Invariant.into());
        }
        if let Some((table, _)) = cache.as_mut()
            && let Some(expression) = table.get(
                entry.slot.ok_or(ResourceError::Invariant)?,
                use_site.arguments,
                expressions,
                b,
            )?
        {
            b.observe(Event::Reductions, 1);
            return Ok(DeltaStep::Unfolded {
                expression,
                path: next,
            });
        }
        let expression = expressions.with_universe_substitution(
            levels,
            names,
            Instance {
                expression_end: use_site.expression_end,
                level_end: use_site.level_end,
                parameters: entry.parameters,
                replacements: use_site.arguments,
            },
            b,
            |substitution| substitution.apply(body),
        )?;
        // Publish only after the entire construction, including scratch retirement.
        if let Some((table, session)) = cache {
            table.insert(
                entry.slot.ok_or(ResourceError::Invariant)?,
                use_site.arguments,
                expression,
                session,
                b,
            )?;
        }
        // Completed original-template delta transport is one actual rewrite.
        b.observe(Event::Reductions, 1);
        Ok(DeltaStep::Unfolded {
            expression,
            path: next,
        })
    }
}
