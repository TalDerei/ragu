use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct ElementInvertInstance;

impl CircuitInstance for ElementInvertInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let input = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        // `Element::invert` computes the inverse internally. Under
        // `MaybeKind = Empty` the inverse-computation closure is erased, so
        // the emitted trace is identical to `invert_with`'s.
        let result = input.invert(dr)?;

        WireCollector::collect_from(&result)
    }
}
