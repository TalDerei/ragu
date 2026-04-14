//! Wire allocation.
//!
//! The core [`Driver`] trait has no notion of allocating a single wire — its
//! primitive is [`gate`](ragu_core::drivers::DriverTypes::gate), which
//! produces four wires at a time. Circuit code frequently needs standalone
//! wires, so this module introduces allocation as a separate concern.
//!
//! A gate's four wires $(A, B, C, D)$ are constrained by $A \cdot B = C$ and
//! $C \cdot D = 0$. When $A$ and $C$ are both zero the remaining wires $B$
//! and $D$ are unconstrained, so up to two independent values can be packed
//! into one gate. An [`Allocator`] manages this: it decides whether to
//! allocate a fresh gate or repurpose a leftover wire from a previous one.
//!
//! Allocation is a trait because different contexts call for different
//! strategies:
//!
//! - [`Allocator`] for `()` — stateless; allocates a full gate per wire.
//!   Simple but wasteful.
//!
//! - [`SimpleAllocator`] — pairs consecutive allocations into one gate,
//!   stashing the spare wire from the first call for the second. Halves
//!   gate cost for sequences of allocations.

use ragu_arithmetic::Coeff;
use ragu_core::{Result, drivers::Driver};

/// Allocates wires on behalf of a gadget.
///
/// Implementations decide how to turn a witness-producing closure into a
/// driver wire. The simplest implementation (see the impl for `()`)
/// allocates a full multiplication gate with zeroed $a$ and $c$ wires.
/// [`SimpleAllocator`] pairs two consecutive allocations into a
/// single gate by stashing the [`Extra`](ragu_core::drivers::DriverTypes::Extra)
/// token that the `()` allocator discards.
pub trait Allocator<'dr, D: Driver<'dr>> {
    /// Allocates a new wire whose value is supplied by `value`.
    ///
    /// The closure follows the same purity contract as [`Driver::mul`]:
    /// it may be called zero or more times, it must be side-effect-free,
    /// and errors returned from it propagate to the caller.
    fn alloc(&mut self, dr: &mut D, value: impl Fn() -> Result<Coeff<D::F>>) -> Result<D::Wire>;
}

/// Stateless allocator that uses one gate per allocation.
///
/// Each call produces a multiplication gate $0 \cdot b = 0$ and returns
/// the $b$ wire, wasting the $a$ and $c$ wires.
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
/// This is the standard paired-allocation strategy. Gadgets that perform
/// many allocations should use `SimpleAllocator` to halve gate cost.
///
/// Dropping a `SimpleAllocator` that still holds a stashed token is safe:
/// the driver already assigned $D = 0$ for that gate.
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
