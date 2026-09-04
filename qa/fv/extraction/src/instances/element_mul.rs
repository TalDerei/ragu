use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, InstanceDriver, WireCollector, WireDeserializer};

pub struct ElementMulInstance;

impl CircuitInstance for ElementMulInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        let input_wires_x = dr.alloc_input_wires(1);
        let input_wires_y = dr.alloc_input_wires(1);

        // Reuse a constant element as a structural template, then substitute the
        // raw input wire into its single-field gadget.
        let element_template = Element::constant(dr, Fp::zero());
        let x = WireDeserializer::new(input_wires_x).into_gadget(&element_template)?;
        let y = WireDeserializer::new(input_wires_y).into_gadget(&element_template)?;

        let z = x.mul(dr, &y)?;

        WireCollector::collect_from(&z)
    }
}
