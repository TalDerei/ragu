use ff::Field;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, FvDriver, WireCollector, WireDeserializer};

pub struct ElementIsEqualInstance;

impl CircuitInstance for ElementIsEqualInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        let a_wires = dr.alloc_input_wires(1);
        let b_wires = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::ZERO);
        let a = WireDeserializer::new(a_wires).into_gadget(&element_template)?;
        let b = WireDeserializer::new(b_wires).into_gadget(&element_template)?;

        // `Element::is_equal` delegates to `sub` (virtual) then `is_zero`.
        // Emits the same 6 wires + 6 asserts as `Boolean.IsZero`, but the
        // `enforce_equal`s pin the first factor to `a - b` rather than a
        // direct input.
        let result = a.is_equal(dr, &mut (), &b)?;

        WireCollector::collect_from(&result)
    }
}
