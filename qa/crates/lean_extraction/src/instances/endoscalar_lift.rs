use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::fv_utils;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector, boolean_from_wire},
};

pub struct EndoscalarLiftInstance;

impl CircuitInstance for EndoscalarLiftInstance {
    type Field = Fp;

    /// Drives the real `Endoscalar::lift` on an `Endoscalar` assembled from the
    /// 128 input wires (see [`boolean_from_wire`] and
    /// `fv_utils::endoscalar_unchecked`).
    ///
    /// Input wires: `bits[0..128]`, least significant first. Output: the lifted
    /// element.
    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        let bits: Vec<_> = dr
            .alloc_input_wires(128)
            .into_iter()
            .map(boolean_from_wire)
            .collect();
        let endo = fv_utils::endoscalar_unchecked(&bits, ExtractionDriver::<Fp>::just(|| 0u128))?;

        let lifted = endo.lift(dr)?;

        WireCollector::collect_from(&lifted)
    }
}
