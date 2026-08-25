use ragu_arithmetic::Coeff;
use ragu_pasta::Fp;

use crate::instance::{CircuitInstance, FvDriver};

pub struct CoreMulInstance;

impl CircuitInstance for CoreMulInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        // MaybeKind = Empty: the closure is never called.
        let (x, y, z) = dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
        Ok(vec![x, y, z])
    }
}
