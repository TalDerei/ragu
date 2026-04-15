//! Pool-based wire allocation.
//!
//! The [`Allocator`] trait abstracts a pool of spare
//! [`Extra`](super::drivers::DriverTypes::Extra) tokens. Drivers that support
//! pooled allocation store an allocator internally and consult it in their
//! [`alloc`](super::drivers::Driver::alloc) and
//! [`donate_extra`](super::drivers::Driver::donate_extra) overrides.
//!
//! [`PoolAllocator`] is the standard implementation backed by a `Vec`.

use alloc::vec::Vec;

/// A pool of spare [`Extra`](super::drivers::DriverTypes::Extra) tokens.
///
/// Drivers compose with an `Allocator` to reuse unconstrained $D$ wires
/// from previous gates, avoiding fresh gate allocation when a spare token
/// is available.
pub trait Allocator<E> {
    /// Attempts to redeem a spare token from the pool.
    fn redeem(&mut self) -> Option<E>;

    /// Donates a spare token to the pool for future use.
    fn donate(&mut self, extra: E);
}

/// Pool allocator backed by a `Vec`.
///
/// Tokens donated via [`donate`](Allocator::donate) are pushed onto the
/// pool; [`redeem`](Allocator::redeem) pops the most recently donated
/// token. Dropping a `PoolAllocator` with tokens still in the pool is
/// safe: the driver already assigned $D = 0$ for those gates.
pub struct PoolAllocator<E> {
    pool: Vec<E>,
}

impl<E> Default for PoolAllocator<E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E> PoolAllocator<E> {
    /// Creates a new `PoolAllocator` with an empty pool.
    pub const fn new() -> Self {
        Self { pool: Vec::new() }
    }
}

impl<E> Allocator<E> for PoolAllocator<E> {
    fn redeem(&mut self) -> Option<E> {
        self.pool.pop()
    }

    fn donate(&mut self, extra: E) {
        self.pool.push(extra);
    }
}
