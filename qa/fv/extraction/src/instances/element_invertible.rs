use ff::Field;
use ragu_pasta::Fp;
use ragu_primitives::Invertible;

use crate::instance::{CircuitInstance, InstanceDriver, WireCollector};

/// `Invertible::alloc_with_advice`: one mul gate `(a, b, c)` carrying the
/// value and its inverse as witness input, followed by `enforce_equal(c, ONE)`.
///
/// `Invertible::alloc` produces the same trace — it only computes the inverse
/// witness before delegating here, and `MaybeKind = Empty` means the closure
/// is never called under extraction — so this instance covers both.
///
/// No input wires (allocation). Outputs: the element and inverse wires.
/// `WireCollector` traverses the `Gadget` representation rather than the
/// one-wire `Write` encoding, so both fields are part of the fingerprint.
pub struct ElementInvertibleInstance;

impl CircuitInstance for ElementInvertibleInstance {
    type Field = Fp;

    fn circuit<'dr, D>(dr: &mut D) -> ragu_core::Result<Vec<D::Wire>>
    where
        D: InstanceDriver<'dr, F = Fp>,
    {
        // MaybeKind = Empty: neither assignment closure is ever called.
        let value = D::just(|| Fp::ZERO);
        let inverse_value = D::just(|| Fp::ZERO);

        let invertible = Invertible::alloc_with_advice(dr, value, inverse_value)?;

        WireCollector::collect_from(&invertible)
    }
}
