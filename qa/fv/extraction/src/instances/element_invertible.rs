use ff::Field;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::Invertible;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

/// `Invertible::alloc_with_advice`: one mul gate `(a, b, c)` carrying the
/// value and its inverse as witness input, followed by `enforce_equal(c, ONE)`.
///
/// `Invertible::alloc` produces the same trace — it only computes the inverse
/// witness before delegating here, and `MaybeKind = Empty` means the closure
/// is never called under extraction — so this instance covers both.
///
/// No input wires (allocation). Output: the element wire; `Write for
/// Invertible` omits the inverse, which stays pinned by the `c = 1`
/// assertion inside the trace.
pub struct ElementInvertibleInstance;

impl CircuitInstance for ElementInvertibleInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // MaybeKind = Empty: neither assignment closure is ever called.
        let value = ExtractionDriver::<Fp>::just(|| Fp::ZERO);
        let inverse_value = ExtractionDriver::<Fp>::just(|| Fp::ZERO);

        let invertible = Invertible::alloc_with_advice(dr, value, inverse_value)?;

        WireCollector::collect_from(&invertible)
    }
}
