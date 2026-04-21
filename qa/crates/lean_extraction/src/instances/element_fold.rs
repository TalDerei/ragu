use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct ElementFoldInstance;

impl CircuitInstance for ElementFoldInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // Length 3: representative of the variadic `Element::fold`. The
        // scale factor is itself an input wire (not a compile-time parameter).
        let input_wires_0 = dr.alloc_input_wires(1);
        let input_wires_1 = dr.alloc_input_wires(1);
        let input_wires_2 = dr.alloc_input_wires(1);
        let scale_wires = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let x0 = WireDeserializer::new(input_wires_0).into_gadget(&element_template)?;
        let x1 = WireDeserializer::new(input_wires_1).into_gadget(&element_template)?;
        let x2 = WireDeserializer::new(input_wires_2).into_gadget(&element_template)?;
        let scale = WireDeserializer::new(scale_wires).into_gadget(&element_template)?;

        let result = Element::fold(dr, [&x0, &x1, &x2], &scale)?;

        WireCollector::collect_from(&result)
    }
}
