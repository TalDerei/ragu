use ff::WithSmallOrderMulGroup;
use ragu_arithmetic::Coeff;
use ragu_core::drivers::{Driver, LinearExpression};
use ragu_pasta::Fp;

use crate::{driver::ExtractionDriver, expr::Expr, instance::CircuitInstance};

pub struct PointConditionalEndoInstance;

impl CircuitInstance for PointConditionalEndoInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let cond_wires = dr.alloc_input_wires(1);
        let point_wires = dr.alloc_input_wires(2);

        let cond_wire = cond_wires[0].clone();
        let point_x = point_wires[0].clone();
        let point_y = point_wires[1].clone();

        // Inline of `input_point.conditional_endo(cond)` to avoid wrapping the
        // raw `cond` input wire as a `Boolean`. The composite is:
        //   endo_x = x · ζ                                  (virtual)
        //   selected_x = cond.conditional_select(x, endo_x)
        //              = x + cond · (endo_x − x)
        //                 inner: diff = endo_x − x          (virtual)
        //                        cond_diff = cond · diff    (mul + 2 enforce_equals)
        //                        selected_x = x + cond_diff (virtual)
        //   y is unchanged.
        let endo_x = dr.add(|lc| {
            lc.add_term(
                &point_x,
                Coeff::Arbitrary(<Fp as WithSmallOrderMulGroup<3>>::ZETA),
            )
        });
        let diff = dr.add(|lc| lc.add(&endo_x).sub(&point_x));
        let (mul_a, mul_b, mul_c) = dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
        dr.enforce_equal(&mul_a, &cond_wire)?;
        dr.enforce_equal(&mul_b, &diff)?;
        let selected_x = dr.add(|lc| lc.add(&point_x).add(&mul_c));

        Ok(vec![selected_x, point_y])
    }
}
