use ragu_arithmetic::Coeff;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::CircuitInstance,
};

pub struct CoreAllocMulInstance;

impl CircuitInstance for CoreAllocMulInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // MaybeKind = Empty: the closure is never called.
        let (x, y, z) = dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
        Ok(vec![x, y, z])
    }
}
