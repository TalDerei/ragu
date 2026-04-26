use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::drivers::{Driver, LinearExpression};
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, WireDeserializer},
};

pub struct BooleanConditionalSelectInstance;

impl CircuitInstance for BooleanConditionalSelectInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let a_wires = dr.alloc_input_wires(1);
        let b_wires = dr.alloc_input_wires(1);

        let cond_wire = cond_wires[0].clone();

        let element_template = Element::constant(dr, Fp::ZERO);
        let a = WireDeserializer::new(a_wires).into_gadget(&element_template)?;
        let b = WireDeserializer::new(b_wires).into_gadget(&element_template)?;

        // Inline of `cond.conditional_select(a, b)` to avoid wrapping the raw
        // `cond` input wire as a `Boolean`. The composite is:
        //   diff = b - a                (virtual)
        //   cond_times_diff = cond · diff   (one mul gate + 2 enforce_equals)
        //   result = a + cond_times_diff    (virtual)
        let diff_wire = dr.add(|lc| lc.add(b.wire()).sub(a.wire()));
        let (mul_a, mul_b, mul_c) = dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
        dr.enforce_equal(&mul_a, &cond_wire)?;
        dr.enforce_equal(&mul_b, &diff_wire)?;
        let result_wire = dr.add(|lc| lc.add(a.wire()).add(&mul_c));

        let result = Element::promote(result_wire, ExtractionDriver::<Fp>::just(|| Fp::ZERO));
        WireCollector::collect_from(&result)
    }
}
