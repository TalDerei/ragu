use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireDeserializer},
};

pub struct ElementEnforceRootOfUnityInstance;

impl CircuitInstance for ElementEnforceRootOfUnityInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_wires = dr.alloc_input_wires(1);

        let element_template = Element::constant(dr, Fp::zero());
        let input = WireDeserializer::new(input_wires).into_gadget(&element_template)?;

        // k = 2: enforce `self^4 = 1`. This is the smallest non-trivial case
        // (k = 0 is `self = 1`, k = 1 is `self^2 = 1`). Other values of k
        // require analogous instances with the appropriate number of squares.
        input.enforce_root_of_unity(dr, 2)?;

        // No output wires; the gadget is an action, not a value.
        Ok(Vec::new())
    }
}
