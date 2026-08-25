use ragu_pasta::Fp;

use crate::{
    instance::{CircuitInstance, InstanceDriver, WireCollector},
    wire_remap::{boolean_from_wire, endoscalar_from_bits},
};

pub struct EndoscalarLiftInstance;

impl CircuitInstance for EndoscalarLiftInstance {
    type Field = Fp;

    /// Drives the real `Endoscalar::lift` on an `Endoscalar` assembled from the
    /// 128 input wires (see [`boolean_from_wire`] and [`endoscalar_from_bits`]).
    ///
    /// Input wires: `bits[0..128]`, least significant first. Output: the lifted
    /// element.
    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        let bits: Vec<_> = dr
            .alloc_input_wires(128)
            .into_iter()
            .map(boolean_from_wire)
            .collect::<ragu_core::Result<_>>()?;
        let endo = endoscalar_from_bits(&bits)?;

        let lifted = endo.lift(dr)?;

        WireCollector::collect_from(&lifted)
    }
}
