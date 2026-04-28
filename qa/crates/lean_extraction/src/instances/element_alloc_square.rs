use ff::Field;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::Element;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct ElementAllocSquareInstance;

impl CircuitInstance for ElementAllocSquareInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // MaybeKind = Empty: the closure is never called.
        let assignment = ExtractionDriver::<Fp>::just(|| Fp::ZERO);
        let (a, a_sq) = Element::alloc_square(dr, assignment)?;

        let mut wires = WireCollector::collect_from(&a)?;
        let mut a_sq_wires = WireCollector::collect_from(&a_sq)?;
        wires.append(&mut a_sq_wires);
        Ok(wires)
    }
}
