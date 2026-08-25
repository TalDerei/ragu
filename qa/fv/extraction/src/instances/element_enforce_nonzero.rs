use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, InstanceDriver, WireCollector, WireDeserializer};

pub struct ElementEnforceNonzeroInstance;

impl CircuitInstance for ElementEnforceNonzeroInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        // Extracts `Element::enforce_nonzero` as a standalone lemma circuit:
        // the discharge that every `NonzeroBank::scope` and every
        // `Element::divide` ultimately depends on. Returns the `Nonzero`
        // wire (Rust's `enforce_nonzero(self) -> Nonzero(self)`), which
        // `Element::divide` links against. Lean reimpl spec:
        // `out = input ∧ input ≠ 0`.
        let input_wires = dr.alloc_input_wires(1);
        let element_template = Element::constant(dr, Fp::zero());
        let elem = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        let nonzero = elem.enforce_nonzero(dr)?;

        WireCollector::collect_from(&nonzero)
    }
}
