//! Move only exactly matched imported associations beyond generated cleanup.
use super::*;
impl Queue {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn capture_publication(
        &self,
        request: &Request<'_>,
        order: &Order,
        derived: &mut recursors::Derived,
        output: &mut Publication,
        work: &mut Working<'_>,
        environment: &mut Environment,
    ) -> Result<(), Stop> {
        if output.ready
            || !output.families.is_empty()
            || !output.constructors.is_empty()
            || !output.recursors.is_empty()
            || derived.exported.len() != derived.types.len()
        {
            return Err(ResourceError::Invariant.into());
        }
        output.before = environment.len();
        output.recursive = derived.recursive;
        for &index in &order.families {
            push(&mut output.families, index, work.budget)?;
        }
        for &index in &order.constructors {
            push(&mut output.constructors, index, work.budget)?;
        }
        for (index, row) in derived.types.iter().enumerate() {
            let (family, constructor_params) = if let Some(&original) = order.families.get(index) {
                (
                    request.types[original as usize].name,
                    request.types[original as usize].num_params,
                )
            } else {
                let helper = self
                    .families
                    .get(index - order.families.len())
                    .ok_or(ResourceError::Invariant)?;
                let prior = environment
                    .inductive(helper.prior, environment.len(), work.names, work.budget)?
                    .ok_or(ResourceError::Invariant)?;
                (helper.prior, prior.num_params)
            };
            push(
                &mut output.recursors,
                super::super::publication::Recursor {
                    exported: derived.exported[index],
                    family,
                    indices: row.indices,
                    constructor_params,
                },
                work.budget,
            )?;
        }
        let phase = derived.phase.take().ok_or(ResourceError::Invariant)?;
        let checkpoint = derived.checkpoint.take().ok_or(ResourceError::Invariant)?;
        environment.retire_signature_stage(checkpoint, phase, work.names, work.budget)?;
        // Readiness follows retirement of all generated signatures. Callback
        // cleanup must still succeed before a public stage can be created.
        output.ready = true;
        Ok(())
    }
}
