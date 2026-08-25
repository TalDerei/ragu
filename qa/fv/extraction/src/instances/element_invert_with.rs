use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, FvDriver, WireCollector, WireDeserializer};

pub struct ElementInvertWithInstance;

impl CircuitInstance for ElementInvertWithInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        let input_wires = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let input = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        // MaybeKind = Empty: the inverse closure is never called.
        let inverse = D::just(Fp::zero);
        let result = input.invert_with(dr, inverse)?;

        WireCollector::collect_from(&result)
    }
}
