use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, InstanceDriver, WireCollector, WireDeserializer};

/// `Element::enforce_invertible`: allocate an `Invertible` pair for this
/// element's value and link the pair's element wire to the input wire.
/// `enforce_invertible_with` shares this trace, differing only in taking the
/// inverse as advice rather than computing it, and witness bodies are never
/// executed under extraction.
///
/// The operations coincide with [`ElementEnforceNonzeroInstance`] — Rust's
/// `enforce_nonzero` is `enforce_invertible(...).into_element()` — but the
/// collected wires do not: `Invertible` carries element *and* inverse, so
/// this trace has two outputs where `Nonzero` has one. That is what pins the
/// gate's second wire as the inverse.
///
/// Input wire: the element (1 wire). Outputs: element and inverse (2 wires).
///
/// [`ElementEnforceNonzeroInstance`]: super::element_enforce_nonzero::ElementEnforceNonzeroInstance
pub struct ElementEnforceInvertibleInstance;

impl CircuitInstance for ElementEnforceInvertibleInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        let input_wires = dr.alloc_input_wires(1);
        let element_template = Element::constant(dr, Fp::zero());
        let elem = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        let invertible = elem.enforce_invertible(dr)?;

        WireCollector::collect_from(&invertible)
    }
}
