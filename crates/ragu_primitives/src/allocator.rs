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
//! - [`SimpleAllocator`] — pairs consecutive allocations into one gate,
//!   stashing the `Extra` token from the first allocation for use by the
//!   second. This halves the number of gates consumed by pure allocations.

use ragu_arithmetic::Coeff;
use ragu_core::{Result, drivers::Driver};

/// Allocates wires on behalf of a gadget.
///
/// Implementations decide how to turn a witness-producing closure into a
/// driver wire. The simplest implementation imitates the default
/// [`Driver::alloc`] body (see the impl for `()`).
/// [`SimpleAllocator`] pairs two consecutive allocations into a
/// single gate by stashing the [`Extra`](ragu_core::drivers::DriverTypes::Extra)
/// token that [`Driver::alloc`]'s default discards.
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

/// Allocator that pairs consecutive allocations into a single gate.
///
/// Each gate allocates four wires $(A, B, C, D)$ with the constraints
/// $A \cdot B = C$ and $C \cdot D = 0$. When $A$ and $C$ are both zero the
/// gate is unconstrained over $B$ and $D$, so two independent values can be
/// packed into one gate. `SimpleAllocator` exploits this: the first call
/// allocates a gate with $A = C = 0$, returns the $B$ wire, and stashes the
/// [`Extra`](ragu_core::drivers::DriverTypes::Extra) token for the $D$ wire.
/// The second call redeems that token via
/// [`assign_extra`](ragu_core::drivers::DriverTypes::assign_extra),
/// returning $D$ without allocating a new gate.
///
/// This is the same paired-allocation strategy used internally by the
/// production prover drivers; `SimpleAllocator` makes it available to
/// gadget code through the [`Allocator`] trait so that gadgets which
/// perform many allocations can opt into the optimization without relying
/// on a driver-level [`Driver::alloc`] override.
///
/// Dropping a `SimpleAllocator` that still holds a stashed token leaves
/// that gate's $D$ wire assigned to zero, which is always safe: the gate
/// has $C = 0$, so $C \cdot D = 0$ holds regardless.
pub struct SimpleAllocator<E> {
    stash: Option<E>,
}

impl<E> Default for SimpleAllocator<E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E> SimpleAllocator<E> {
    /// Creates a new `SimpleAllocator` with no stashed token.
    pub const fn new() -> Self {
        Self { stash: None }
    }
}

impl<'dr, D: Driver<'dr>> Allocator<'dr, D> for SimpleAllocator<D::Extra> {
    fn alloc(&mut self, dr: &mut D, value: impl Fn() -> Result<Coeff<D::F>>) -> Result<D::Wire> {
        if let Some(extra) = self.stash.take() {
            dr.assign_extra(extra, value)
        } else {
            let (_, b, _, extra) = dr.gate(|| Ok((Coeff::Zero, value()?, Coeff::Zero)))?;
            self.stash = Some(extra);
            Ok(b)
        }
    }
}
