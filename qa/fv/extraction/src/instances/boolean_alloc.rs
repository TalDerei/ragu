use ragu_pasta::Fp;
use ragu_primitives::Boolean;

use crate::instance::{CircuitInstance, FvDriver, WireCollector};

pub struct BooleanAllocInstance;

impl CircuitInstance for BooleanAllocInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: FvDriver<'dr, F = Fp>,
    {
        // MaybeKind = Empty: the bool-value closure is never called.
        let value = D::just(|| false);
        let boolean = Boolean::alloc(dr, &mut (), value)?;
        WireCollector::collect_from(&boolean)
    }
}
