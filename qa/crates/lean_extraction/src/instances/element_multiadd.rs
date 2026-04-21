use ragu_pasta::Fp;
use ragu_primitives::{Element, multiadd};

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct ElementMultiaddInstance;

impl CircuitInstance for ElementMultiaddInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // Length 3: representative of the variadic `multiadd`.
        let input_wires_0 = dr.alloc_input_wires(1);
        let input_wires_1 = dr.alloc_input_wires(1);
        let input_wires_2 = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let x0 = WireDeserializer::new(input_wires_0).into_gadget(&element_template)?;
        let x1 = WireDeserializer::new(input_wires_1).into_gadget(&element_template)?;
        let x2 = WireDeserializer::new(input_wires_2).into_gadget(&element_template)?;

        // Representative coefficients. Distinct primes from Scale's 5 and
        // AddCoeff's 7 so the autogen constants are visually distinguishable.
        let coeffs = [Fp::from(11), Fp::from(13), Fp::from(17)];
        let values = [x0, x1, x2];
        let result = multiadd(dr, &values, &coeffs);

        WireCollector::collect_from(&result)
    }
}
