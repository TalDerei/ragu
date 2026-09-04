use ff::Field;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, InstanceDriver, WireCollector};

pub struct ElementAllocInstance;

impl CircuitInstance for ElementAllocInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        // MaybeKind = Empty: the assignment closure is never called.
        let assignment = D::just(|| Fp::ZERO);
        // Use the trivial `()` allocator: one mul gate per alloc, wastes A and C.
        // Structurally equivalent to `Core::Mul` projected to the middle wire.
        let element = Element::alloc(dr, &mut (), assignment)?;
        WireCollector::collect_from(&element)
    }
}
