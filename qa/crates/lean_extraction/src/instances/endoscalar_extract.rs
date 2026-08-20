use ragu_pasta::Fp;
use ragu_primitives::{Element, Endoscalar, EndoscalarChallenge};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct EndoscalarExtractInstance;

impl CircuitInstance for EndoscalarExtractInstance {
    type Field = Fp;

    /// Drives the real `EndoscalarChallenge::from_element` followed by
    /// `Endoscalar::extract` — the in-circuit path `compute_v` takes — on a
    /// single input wire holding the challenge element.
    ///
    /// `from_element` emits `Fp::CAPACITY` (254) `Boolean::alloc` gates and
    /// one recomposition constraint binding their weighted sum to the element
    /// (`boolean.rs::decompose`); `extract` emits nothing and returns the low
    /// 128 bits. Under `MaybeKind = Empty` the witness-side range check
    /// (`try_just`) and the per-bit witness closures never run, so the trace
    /// is exactly those constraints.
    ///
    /// Input wire: `elem` (1 wire). Output: the 128 endoscalar bit wires,
    /// least significant first.
    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires = dr.alloc_input_wires(1);
        let element_template = Element::constant(dr, Fp::zero());
        let elem = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        let challenge = EndoscalarChallenge::from_element(dr, &mut (), elem)?;
        let endo = Endoscalar::extract(challenge);

        WireCollector::collect_from(&endo)
    }
}
