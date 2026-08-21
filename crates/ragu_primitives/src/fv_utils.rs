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

use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
};

use crate::{Boolean, Endoscalar, promotion::Demoted, vec::CollectFixed};

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

/// Assembles an [`Endoscalar`] from its 128 bits, least significant first,
/// **without** any check that they are booleans.
///
/// `value` is the witness the bits are supposed to encode; nothing ties the
/// two together (exactly as with [`Endoscalar::alloc`], whose `value` is also
/// unconstrained witness data). The extraction instances use this to hand
/// input-wire booleans to the real `Endoscalar::lift` / `group_scale`.
///
/// # Errors
///
/// Fails unless exactly 128 bits are given.
pub fn endoscalar_unchecked<'dr, D: Driver<'dr>>(
    bits: &[Boolean<'dr, D>],
    value: DriverValue<D, u128>,
) -> Result<Endoscalar<'dr, D>> {
    let bits = bits.iter().map(Demoted::new).try_collect_fixed()?;
    Ok(Endoscalar::new_unchecked(bits, value))
}
