use ff::Field;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    instance::{CircuitInstance, InstanceDriver, WireDeserializer},
    wire_remap::boolean_from_wire,
};

pub struct BooleanConditionalEnforceEqualInstance;

impl CircuitInstance for BooleanConditionalEnforceEqualInstance {
    type Field = Fp;

    /// Drives the real `Boolean::conditional_enforce_equal(a, b)` with the
    /// condition input wire wrapped as a `Boolean` (see [`boolean_from_wire`]).
    /// The gadget's spare `D` wire goes to the unit allocator, which the
    /// extractor's three-wire model makes trace-neutral.
    ///
    /// Input wires: `cond`, `a`, `b`. No output wires; the gadget is an
    /// assertion, not a value.
    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        let cond_wires = dr.alloc_input_wires(1);
        let a_wires = dr.alloc_input_wires(1);
        let b_wires = dr.alloc_input_wires(1);

        let cond = boolean_from_wire(cond_wires[0].clone())?;
        let element_template = Element::constant(dr, Fp::ZERO);
        let a = WireDeserializer::new(a_wires).into_gadget(&element_template)?;
        let b = WireDeserializer::new(b_wires).into_gadget(&element_template)?;

        cond.conditional_enforce_equal(dr, &mut (), &a, &b)?;

        Ok(Vec::new())
    }
}
