use ragu_pasta::Fp;
use ragu_primitives::Endoscalar;

use crate::instance::{CircuitInstance, InstanceDriver, WireCollector};

pub struct EndoscalarAllocInstance;

impl CircuitInstance for EndoscalarAllocInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        // MaybeKind = Empty: the u128-value closure threaded into the
        // per-bit `Boolean::alloc` calls is never executed under extraction.
        let value = D::just(|| 0u128);
        let endo = Endoscalar::alloc(dr, value)?;
        WireCollector::collect_from(&endo)
    }
}
