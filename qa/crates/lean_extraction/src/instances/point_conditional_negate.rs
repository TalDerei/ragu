use ragu_arithmetic::Coeff;
use ragu_core::drivers::{Driver, LinearExpression};
use ragu_pasta::Fp;

use crate::{driver::ExtractionDriver, expr::Expr, instance::CircuitInstance};

pub struct PointConditionalNegateInstance;

impl CircuitInstance for PointConditionalNegateInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let point_wires = dr.alloc_input_wires(2);

        let cond_wire = cond_wires[0].clone();
        let point_x = point_wires[0].clone();
        let point_y = point_wires[1].clone();

        // Inline of `input_point.conditional_negate(cond)` to avoid wrapping the
        // raw `cond` input wire as a `Boolean`. The composite is:
        //   neg_y = −y                                        (virtual)
        //   selected_y = cond.conditional_select(y, neg_y)
        //              = y + cond · (neg_y − y)
        //                 inner: diff = neg_y − y             (virtual)
        //                        cond_diff = cond · diff      (mul + 2 enforce_equals)
        //                        selected_y = y + cond_diff   (virtual)
        //   x is unchanged.
        let neg_y = dr.add(|lc| lc.add_term(&point_y, Coeff::NegativeOne));
        let diff = dr.add(|lc| lc.add(&neg_y).sub(&point_y));
        let (mul_a, mul_b, mul_c) = dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
        dr.enforce_equal(&mul_a, &cond_wire)?;
        dr.enforce_equal(&mul_b, &diff)?;
        let selected_y = dr.add(|lc| lc.add(&point_y).add(&mul_c));

        Ok(vec![point_x, selected_y])
    }
}
