//! Allocator abstraction for gadgets.
//!
//! [`Allocator`] decouples the decision of *how* to allocate a wire from the
//! driver currently running synthesis. [`Driver::alloc`] has a wasteful
//! default implementation (it allocates a multiplication gate with zeroed
//! $a$ and $c$ wires), and drivers may override it — but that override is
//! an all-or-nothing, driver-wide choice. An [`Allocator`] lives one level
//! above the driver: gadget code asks an allocator to allocate, and the
//! allocator decides whether to pack this allocation into a shared gate,
//! forward to [`Driver::alloc`], or do something else entirely.
//!
//! This module ships two implementations:
//!
//! - [`Allocator`] for `()` — a stateless allocator that mirrors the
//!   wasteful default [`Driver::alloc`] body by calling [`Driver::mul`]
//!   with zeroed $a$ and $c$ wires. Suited to callers that want the
//!   cost model to reflect the default [`Driver::alloc`] regardless of
//!   whether the running driver overrides it.
//!
//! - [`StubAllocator`] — forwards each allocation to [`Driver::alloc`]
//!   without modification, preserving any driver-level override. Use this
//!   when the call site should behave identically to a direct
//!   [`Driver::alloc`] call.

use ragu_arithmetic::Coeff;
use ragu_core::{Result, drivers::Driver};

/// Allocates wires on behalf of a gadget.
///
/// Implementations decide how to turn a witness-producing closure into a
/// driver wire. The simplest implementations forward to [`Driver::alloc`]
/// (see [`StubAllocator`]) or imitate its default body (see the impl for
/// `()`). A batching implementation can pair two consecutive allocations
/// into a single $a \cdot b = c$ gate, reusing the $a$ and $c$ wires that
/// [`Driver::alloc`]'s default leaves zeroed.
pub trait Allocator<'dr, D: Driver<'dr>> {
    /// Allocates a new wire whose value is supplied by `value`.
    ///
    /// The closure follows the same purity contract as [`Driver::alloc`]:
    /// it may be called zero or more times, it must be side-effect-free,
    /// and errors returned from it propagate to the caller.
    fn alloc(&mut self, dr: &mut D, value: impl Fn() -> Result<Coeff<D::F>>) -> Result<D::Wire>;
}

/// Stateless allocator that mirrors the default [`Driver::alloc`] body.
///
/// Each call produces a multiplication gate $0 \cdot b = 0$ and returns
/// the $b$ wire, wasting the $a$ and $c$ wires. This is useful when the
/// caller wants accounting to reflect that default cost model even against
/// a driver that overrides [`Driver::alloc`] — in particular, against the
/// [`Emulator`](ragu_core::drivers::emulator::Emulator), whose unit-valued
/// `Wire` makes the "wasted" wires free in practice.
impl<'dr, D: Driver<'dr>> Allocator<'dr, D> for () {
    fn alloc(&mut self, dr: &mut D, value: impl Fn() -> Result<Coeff<D::F>>) -> Result<D::Wire> {
        let (_, b, _) = dr.mul(|| Ok((Coeff::Zero, value()?, Coeff::Zero)))?;
        Ok(b)
    }
}

/// Allocator that forwards to [`Driver::alloc`] unchanged, preserving any
/// driver-specific override.
///
/// Use this at call sites that need to respect the running driver's own
/// allocation behavior — for instance, the allocation counter tracked by
/// [`Simulator`](crate::Simulator), or the paired-allocation optimization
/// used by the production prover drivers.
pub struct StubAllocator;

impl<'dr, D: Driver<'dr>> Allocator<'dr, D> for StubAllocator {
    fn alloc(&mut self, dr: &mut D, value: impl Fn() -> Result<Coeff<D::F>>) -> Result<D::Wire> {
        dr.alloc(value)
    }
}
