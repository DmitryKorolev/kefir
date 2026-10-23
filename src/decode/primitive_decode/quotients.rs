//! Decoded quotient descriptors, not validated primitive signatures.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Role {
    Type,
    Constructor,
    Lift,
    Induction,
}
impl Role {
    pub(super) fn parse(kind: &str) -> Result<Self, Cause> {
        match kind {
            "type" => Ok(Self::Type),
            "ctor" => Ok(Self::Constructor),
            "lift" => Ok(Self::Lift),
            "ind" => Ok(Self::Induction),
            _ => Err(Cause::InvalidRecord),
        }
    }
}
/// Handles belong to the originating decoder. The borrowed ordered parameter
/// slice shares ordinary-record scratch, which cannot be reused while live.
/// Role validation is format validation; this request grants no semantic authority.
pub(crate) struct Request<'a> {
    pub role: Role,
    pub name: NameId,
    pub parameters: &'a [NameId],
    pub ty: ExprId,
}
pub(super) struct Fields {
    pub(super) role: Role,
    pub(super) name: NameId,
    pub(super) ty: ExprId,
}
const _: () = assert!(size_of::<Fields>() == 12);
const _: () = assert!(size_of::<Request<'_>>() == 32);
// No additional Scratch owner: ordered parameters use its existing budgeted
// declaration vector, four bytes per NameId plus charged capacity slack. Serde
// temporaries remain within the existing 256N reservation and drop ordering.

impl Decoder {
    /// Only imported ordinals enter here. Generated names have no serialized ID.
    pub(super) fn imported_name_slot(&self, ordinal: u32) -> Result<u32, ResourceError> {
        let [start, len] = self.name_gap;
        if ordinal < start {
            Ok(ordinal)
        } else {
            ordinal.checked_add(len).ok_or(ResourceError::Invariant)
        }
    }

    /// Physical names within the gap must never enter the serialized index.
    pub(super) fn imported_name_ordinal(&self, slot: u32) -> Result<u32, ResourceError> {
        let [start, len] = self.name_gap;
        if slot < start {
            Ok(slot)
        } else {
            let ordinal = slot.checked_sub(len).ok_or(ResourceError::Invariant)?;
            if ordinal < start {
                return Err(ResourceError::Invariant);
            }
            Ok(ordinal)
        }
    }

    /// First quotient initialization only, before declaration_session records
    /// its name watermark. These names then belong to the run's original prefix.
    /// Serialized name_ids retain imported ordinals; name_gap translates them
    /// to physical handles exactly once during typed reference validation.
    /// The semantic owner must abort on any failure; partial appends convey no
    /// quotient authority. All seven fixed String components are valid syntax.
    pub(crate) fn quotient_names(
        &mut self,
        budget: &mut Budget,
    ) -> Result<[NameId; 7], ResourceError> {
        fn append(
            names: &mut Names,
            parent: NameId,
            text: &str,
            b: &mut Budget,
        ) -> Result<NameId, ResourceError> {
            names
                .append(parent, Component::String(text), b)
                .map_err(|error| match error {
                    NameError::Resource(error) => error,
                    NameError::InvalidNumber | NameError::NumericRange => ResourceError::Invariant,
                })
        }
        if self.name_gap[1] != 0 {
            return Err(ResourceError::Invariant);
        }
        let start = u32::try_from(self.names.len()).map_err(|_| ResourceError::Counter)?;
        start.checked_add(7).ok_or(ResourceError::Counter)?;
        // Set before fallible appends: even a partial failure cannot retry this
        // initializer. The caller poisons its owner and ends the run on error.
        self.name_gap = [start, 7];
        let eq = append(&mut self.names, NameId::ANONYMOUS, "Eq", budget)?;
        let quot = append(&mut self.names, NameId::ANONYMOUS, "Quot", budget)?;
        let mk = append(&mut self.names, quot, "mk", budget)?;
        let lift = append(&mut self.names, quot, "lift", budget)?;
        let ind = append(&mut self.names, quot, "ind", budget)?;
        let u = append(&mut self.names, NameId::ANONYMOUS, "u", budget)?;
        let v = append(&mut self.names, NameId::ANONYMOUS, "v", budget)?;
        Ok([eq, quot, mk, lift, ind, u, v])
    }
}
