use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, FvDriver, WireCollector, WireDeserializer};

pub struct ElementSquareInstance;

impl CircuitInstance for ElementSquareInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        let input_wires = dr.alloc_input_wires(1);

        // Reuse a constant element as a structural template, then substitute the
        // raw input wire into its single-field gadget.
        let element_template = Element::constant(dr, Fp::zero());
        let x = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        let z = x.square(dr)?;

        WireCollector::collect_from(&z)
    }
}
