//! Escape hatches for the trace-extraction tooling (`qa/crates/lean_extraction`).
//!
//! This module re-exposes crate-internal constructors that trade in-circuit
//! constraints for an external soundness argument, so the formal-verification
//! instances can mirror gadgets that make that trade-off without cloning their
//! bodies. Each helper is a thin wrapper over a `pub(crate)` constructor, so
//! the constructors themselves stay a single definition.
//!
//! Gated behind the `unstable-fv` feature; not part of the stable public API.

use ragu_core::drivers::Driver;

use crate::NonzeroBank;

/// Constructs an unchecked [`NonzeroBank`], where `fold` emits no constraint
/// and dropping the bank is a no-op.
///
/// The nonzero invariant of every folded element must instead be guaranteed by
/// an external argument (e.g. the Appendix C no-collision bound that
/// [`Endoscalar::group_scale`](crate::Endoscalar::group_scale) relies on).
pub fn nonzero_bank_unchecked<'dr, D: Driver<'dr>>() -> NonzeroBank<'dr, D> {
    NonzeroBank::new_unchecked()
}
