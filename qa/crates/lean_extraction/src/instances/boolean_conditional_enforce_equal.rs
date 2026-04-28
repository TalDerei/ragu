use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::drivers::{Driver, DriverTypes, LinearExpression};
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireDeserializer},
};

pub struct BooleanConditionalEnforceEqualInstance;

impl CircuitInstance for BooleanConditionalEnforceEqualInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let a_wires = dr.alloc_input_wires(1);
        let b_wires = dr.alloc_input_wires(1);

        let cond_wire = cond_wires[0].clone();

        let element_template = Element::constant(dr, Fp::ZERO);
        let a = WireDeserializer::new(a_wires).into_gadget(&element_template)?;
        let b = WireDeserializer::new(b_wires).into_gadget(&element_template)?;

        // Inline of `cond.conditional_enforce_equal(a, b)` to avoid wrapping the
        // raw `cond` input wire as a `Boolean`. Emits one custom 3-wire gate
        // (`cond_g · diff_g = zero_g`) plus three constraints:
        //   * `cond_g = cond` (input)
        //   * `diff_g = a - b`
        //   * `zero_g = 0`
        // Together these enforce `cond · (a - b) = 0` (i.e. `cond = 1 ⇒ a = b`).
        let (cond_g, diff_g, zero_g, _extra) =
            dr.gate(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
        dr.enforce_equal(&cond_g, &cond_wire)?;
        dr.enforce_zero(|lc| lc.add(&diff_g).sub(a.wire()).add(b.wire()))?;
        dr.enforce_zero(|lc| lc.add(&zero_g))?;

        // No output wires; the gadget is an assertion, not a value.
        Ok(Vec::new())
    }
}
