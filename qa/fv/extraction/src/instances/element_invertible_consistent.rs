use ff::Field;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::{Invertible, consistent::Consistent};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireDeserializer},
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

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let template = {
            let mut scratch = ExtractionDriver::<Fp>::new();
            let value = ExtractionDriver::<Fp>::just(|| Fp::ZERO);
            let inverse_value = ExtractionDriver::<Fp>::just(|| Fp::ZERO);
            Invertible::alloc_with_advice(&mut scratch, value, inverse_value)?
        };
        let pair_wires = dr.alloc_input_wires(2);
        let invertible = WireDeserializer::new(pair_wires).into_gadget(&template)?;

        invertible.enforce_consistent(dr)?;

        Ok(Vec::new())
    }
}
