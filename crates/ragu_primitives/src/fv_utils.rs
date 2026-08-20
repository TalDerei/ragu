//! Escape hatches for the trace-extraction tooling (`qa/crates/lean_extraction`).
//!
//! This module exposes crate-internal constructors that bypass a gadget's
//! invariant, so the formal-verification instances can hand their symbolic
//! input wires to the real gadgets instead of re-implementing the gadgets'
//! bodies. Each helper is a thin wrapper over a `pub(crate)` constructor, so
//! the constructors themselves stay a single definition, and this module is
//! the complete list of such hatches.
//!
//! Gated behind the `unstable-fv` feature; not part of the stable public API.
//! `lean_extraction` is its own Cargo workspace precisely so that enabling the
//! feature cannot unify into the library builds.

use ragu_core::drivers::{Driver, DriverValue};

use crate::Boolean;

/// Wraps an existing wire as a [`Boolean`] **without** constraining it.
///
/// Nothing ties `wire` to `0` or `1`; that invariant is the caller's. The
/// extraction instances use this to pass input wires to gadgets that take a
/// `&Boolean` (`Boolean::and`, `Point::conditional_negate`, …); the Lean
/// reimplementations carry the boolean-ness as an `Assumptions`.
pub fn boolean_unchecked<'dr, D: Driver<'dr>>(
    wire: D::Wire,
    value: DriverValue<D, bool>,
) -> Boolean<'dr, D> {
    Boolean::new_unchecked(wire, value)
}
