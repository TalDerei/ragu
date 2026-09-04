use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, InstanceDriver, WireDeserializer};

pub struct ElementEnforceZeroInstance;

impl CircuitInstance for ElementEnforceZeroInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        let input_wires = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let input = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        input.enforce_zero(dr)?;

        // No output wires; the gadget is an action, not a value.
        Ok(Vec::new())
    }
}
