use ff::Field;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct ElementIsZeroInstance;

impl CircuitInstance for ElementIsZeroInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::ZERO);
        let x = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        // `is_zero` is `pub(crate)` in `ragu_primitives::boolean`; the public
        // entry point is `Element::is_zero`, which delegates to it. Emits two
        // gates (6 wires) plus 4 asserts implementing the inverse trick.
        let result = x.is_zero(dr, &mut ())?;

        WireCollector::collect_from(&result)
    }
}
