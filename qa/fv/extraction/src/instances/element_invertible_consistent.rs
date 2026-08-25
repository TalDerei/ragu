use ragu_pasta::Fp;
use ragu_primitives::consistent::Consistent;

use crate::{
    instance::{CircuitInstance, FvDriver},
    wire_remap::invertible_from_wires,
};

/// `Invertible::enforce_consistent` on a pair assembled from two input wires:
/// a fresh `Invertible::alloc_with_advice` seeded from the pair's own values,
/// linked to it wire by wire — both the element and the inverse, since the
/// conservative equality recurses into every `Gadget` field.
///
/// `Invertible` has no constraint-free constructor, so the template that
/// shapes the deserialization is allocated on a scratch driver whose
/// operations are discarded; only its wire layout is used.
///
/// Input wires: `element, inverse` (2 wires). No outputs.
pub struct ElementInvertibleConsistentInstance;

impl CircuitInstance for ElementInvertibleConsistentInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        let pair_wires = dr.alloc_input_wires(2);
        let invertible = invertible_from_wires::<D>(pair_wires)?;

        invertible.enforce_consistent(dr)?;

        Ok(Vec::new())
    }
}
