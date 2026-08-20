use ff::Field;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer, boolean_from_wire},
};

pub struct BooleanConditionalSelectInstance;

impl CircuitInstance for BooleanConditionalSelectInstance {
    type Field = Fp;

    /// Drives the real `Boolean::conditional_select(a, b)` with the condition
    /// input wire wrapped as a `Boolean` (see [`boolean_from_wire`]).
    ///
    /// Input wires: `cond`, `a`, `b`. Output: the selected element.
    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let a_wires = dr.alloc_input_wires(1);
        let b_wires = dr.alloc_input_wires(1);

        let cond = boolean_from_wire(cond_wires[0].clone());
        let element_template = Element::constant(dr, Fp::ZERO);
        let a = WireDeserializer::new(a_wires).into_gadget(&element_template)?;
        let b = WireDeserializer::new(b_wires).into_gadget(&element_template)?;

        let result = cond.conditional_select(dr, &a, &b)?;

        WireCollector::collect_from(&result)
    }
}
