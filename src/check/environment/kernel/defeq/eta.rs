//! Function eta, structure eta and comparison of unit-like values.

use super::*;

impl<'e, 'w> Kernel<'e, 'w> {
    pub(in super::super) fn eta(&mut self, lam: u32, other: u32) -> R<bool> {
        if !matches!(
            self.vals[other as usize],
            Val::Local { .. } | Val::Const { .. } | Val::Lam(_) | Val::Proj { .. }
        ) {
            return Ok(false);
        }
        // As in Lean, the other side's eta-expansion carries its own binder
        // domain, which must equal the lambda's.
        let Some(t) = self.infer_value(other)? else {
            return Ok(false);
        };
        let w = self.whnf(t)?;
        if !matches!(
            self.vals[w as usize],
            Val::Pi(_) | Val::LamTy(_) | Val::Arrow { .. }
        ) {
            return Ok(false);
        }
        let d = self.binder_dom(lam)?;
        let od = self.binder_dom(w)?;
        if !self.defeq(d, od)? {
            return Ok(false);
        }
        let x = self.open_local(d)?;
        let r = (|| {
            let l = self.apply(lam, x)?;
            let o = self.apply(other, x)?;
            self.defeq(l, o)
        })();
        self.close_local();
        r
    }
    #[allow(
        clippy::let_and_return,
        reason = "test-only observer omitted from public source"
    )]
    pub(in super::super) fn struct_eta(&mut self, x: u32, ctor: u32) -> R<bool> {
        let Val::Const { ci, li, spine } = self.vals[ctor as usize] else {
            return Ok(false);
        };
        let Some((family, _)) = self.const_view(ci)?.ctor else {
            return Ok(false);
        };
        let fci = match self.const_by_canon.get(&family) {
            Some(&fci) => fci,
            None => {
                // Committed constructor metadata fixes the original family.
                // Its availability cannot depend on an earlier value having
                // loaded that family's attempt-local CInfo. Resolve it under
                // the same immutable frontier and retain ordinary admission.
                let Some(c) = self.env.constructor(
                    self.const_view(ci)?.name,
                    self.before.min(self.env.len()),
                    self.names,
                    self.b,
                )?
                else {
                    return Ok(false);
                };
                let fci = self.const_info(c.family)?;
                fci
            }
        };
        let Some(ind) = self.const_view(fci)?.ind else {
            return Ok(false);
        };
        if !ind.structure_like() {
            return Ok(false);
        }
        let nf = ind.ctors[0].num_fields;
        if self.cells[spine as usize].len != ind.nparams + nf {
            return Ok(false);
        }
        let (Some(tx), Some(tc)) = (self.infer_value(x)?, self.infer_value(ctor)?) else {
            return Ok(false);
        };
        if !self.defeq(tx, tc)? {
            return Ok(false);
        }
        let Some(args) = self.spine_args_opt(spine)? else {
            return Ok(false);
        };
        let res = (|| {
            if nf == 0 {
                return Ok(true);
            }
            // Conversion's checked-term premise supplies field typing. Equal
            // parent types and earlier compared fields transport the actual
            // constructor domain to x's projection, including dependencies on
            // earlier proofs (by proof irrelevance). Classification alone is
            // never permission to compare an unchecked constructor.
            // Keep the existing restriction on projecting data from Prop.
            let mut typed = match self.prop_status(tc) {
                Ok(Some(false)) => true,
                Ok(_) | Err(KErr::Unsupported) => false,
                Err(error) => return Err(error),
            };
            let (mut fty, mut at) = (NONE, 0usize);
            for i in 0..nf {
                if typed {
                    let status = self.arg_is_proof(
                        &mut fty,
                        &mut at,
                        Err((ci, li)),
                        &args,
                        (ind.nparams + i) as usize,
                    );
                    match status {
                        Ok(Some(true)) => {
                            continue;
                        }
                        Ok(Some(false)) => {}
                        Ok(None) | Err(KErr::Unsupported) => typed = false,
                        Err(error) => return Err(error),
                    }
                }
                let p = self.proj(x, i, fci)?;
                if !self.defeq(p, args[(ind.nparams + i) as usize])? {
                    return Ok(false);
                }
            }
            Ok(true)
        })();
        self.scratch_finish(res, [args])
    }
    pub(super) fn unit_like(&mut self, a: u32, c: u32) -> R<bool> {
        let Some(ta) = self.infer_value(a)? else {
            return Ok(false);
        };
        let w = self.whnf(ta)?;
        let Val::Const { ci, .. } = self.vals[w as usize] else {
            return Ok(false);
        };
        let Some(ind) = self.const_view(ci)?.ind else {
            return Ok(false);
        };
        if !ind.structure_like() || ind.ctors[0].num_fields != 0 {
            return Ok(false);
        }
        let Some(tc) = self.infer_value(c)? else {
            return Ok(false);
        };
        self.defeq(w, tc)
    }
}
