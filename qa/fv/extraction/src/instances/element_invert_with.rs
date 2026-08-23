use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct ElementInvertWithInstance;

impl CircuitInstance for ElementInvertWithInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let input = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        // MaybeKind = Empty: the inverse closure is never called.
        let inverse = ExtractionDriver::<Fp>::just(Fp::zero);
        let result = input.invert_with(dr, inverse)?;

        WireCollector::collect_from(&result)
    }
}
