use ff::Field;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct ElementAllocInstance;

impl CircuitInstance for ElementAllocInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // MaybeKind = Empty: the assignment closure is never called.
        let assignment = ExtractionDriver::<Fp>::just(|| Fp::ZERO);
        // Use the trivial `()` allocator: one mul gate per alloc, wastes A and C.
        // Structurally equivalent to `Core::AllocMul` projected to the middle wire.
        let element = Element::alloc(dr, &mut (), assignment)?;
        WireCollector::collect_from(&element)
    }
}
