use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct ElementSquareInstance;

impl CircuitInstance for ElementSquareInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires = dr.alloc_input_wires(1);

        // Reuse a constant element as a structural template, then substitute the
        // raw input wire into its single-field gadget.
        let element_template = Element::constant(dr, Fp::zero());
        let x = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        let z = x.square(dr)?;

        WireCollector::collect_from(&z)
    }
}
