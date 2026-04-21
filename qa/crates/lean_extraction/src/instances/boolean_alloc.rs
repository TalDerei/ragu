use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::Boolean;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct BooleanAllocInstance;

impl CircuitInstance for BooleanAllocInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // MaybeKind = Empty: the bool-value closure is never called.
        let value = ExtractionDriver::<Fp>::just(|| false);
        let boolean = Boolean::alloc(dr, &mut (), value)?;
        WireCollector::collect_from(&boolean)
    }
}
