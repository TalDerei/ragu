use ff::Field;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::instance::{CircuitInstance, FvDriver, WireCollector};

pub struct ElementAllocSquareInstance;

impl CircuitInstance for ElementAllocSquareInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        // MaybeKind = Empty: the closure is never called.
        let assignment = D::just(|| Fp::ZERO);
        let (a, a_sq) = Element::alloc_square(dr, assignment)?;

        let mut wires = WireCollector::collect_from(&a)?;
        let mut a_sq_wires = WireCollector::collect_from(&a_sq)?;
        wires.append(&mut a_sq_wires);
        Ok(wires)
    }
}
