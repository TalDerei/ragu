use ragu_arithmetic::Coeff;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;

use crate::{driver::ExtractionDriver, expr::Expr, instance::CircuitInstance};

pub struct BooleanAndInstance;

impl CircuitInstance for BooleanAndInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let input_a_wires = dr.alloc_input_wires(1);
        let input_b_wires = dr.alloc_input_wires(1);

        // Inline of `Boolean::and(input_a, input_b)`: one mul gate (`a · b = c`)
        // plus two `enforce_equal`s binding the gate's `a`/`b` wires to the
        // inputs. Returns the gate's `c` wire.
        //
        // We can't wrap the inputs as `Boolean`s without an unsafe `Boolean`
        // constructor; the Lean Spec's `Assumptions` re-establishes the
        // boolean-ness invariant, so the gate-only constraints emitted here
        // suffice for the autogen.
        let (mul_a, mul_b, mul_c) = dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
        dr.enforce_equal(&mul_a, &input_a_wires[0])?;
        dr.enforce_equal(&mul_b, &input_b_wires[0])?;

        Ok(vec![mul_c])
    }
}
