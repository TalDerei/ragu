#![cfg(feature = "unstable-fuzzing")]
#![doc(hidden)]
//! Hooks for the out-of-tree fuzz harness (`qa/fuzz`).
//!
//! Nothing here is part of the crate's API. The module gates itself behind
//! the `unstable-fuzzing` feature with the inner attribute above, so the
//! production modules carry no feature attributes, and it is hidden from the
//! rendered documentation. It may change or disappear in any release.
//!
//! The patcher seam over the internal recursion circuits lives in
//! `fuse::patcher`, a child of the fuse pipeline so that it can call the same
//! private helpers `fuse` does. This module re-exports its vocabulary and
//! wraps its entry points as free functions, so the public types grow no
//! feature-dependent methods.

use ragu_arithmetic::{Cycle, rand::CryptoRng};
use ragu_circuits::polynomials::Rank;
use ragu_core::Result;

pub use crate::fuse::patcher::{CircuitSpec, InternalCircuitVisitor, OutputRef, Resolution};
use crate::{Application, Pcd, SelectableBackend, step::Step};

/// Runs the fuse witness-generation for `step` over `left` and `right` and
/// hands each internal recursion circuit, its [`CircuitSpec`] and its honest
/// witness to `visitor`, in place of tracing them into a proof. See the
/// `fuse::patcher` module docs for what a circuit is held responsible for.
///
/// # Errors
///
/// Propagates any error from witness generation, from laying out a stage, or
/// from the visitor.
pub fn capture_internal_circuits<'source, C, R, const HEADER_SIZE: usize, B, RNG, S, V>(
    app: &Application<'_, C, R, HEADER_SIZE, B>,
    rng: &mut RNG,
    step: S,
    witness: S::Witness<'source>,
    left: Pcd<C, R, S::Left>,
    right: Pcd<C, R, S::Right>,
    visitor: &mut V,
) -> Result<()>
where
    C: Cycle,
    R: Rank,
    B: SelectableBackend,
    RNG: CryptoRng,
    S: Step<C>,
    V: InternalCircuitVisitor<C>,
{
    app.capture_internal_circuits(rng, step, witness, left, right, visitor)
}

/// [`capture_internal_circuits`] at the base case: the fuse
/// [`seed`](Application::seed) performs, over two trivial children. There
/// `outer_collapse` deliberately leaves the final claim free, so its spec
/// drops that slot.
///
/// # Errors
///
/// As [`capture_internal_circuits`].
pub fn capture_internal_circuits_seeded<'source, C, R, const HEADER_SIZE: usize, B, RNG, S, V>(
    app: &Application<'_, C, R, HEADER_SIZE, B>,
    rng: &mut RNG,
    step: S,
    witness: S::Witness<'source>,
    visitor: &mut V,
) -> Result<()>
where
    C: Cycle,
    R: Rank,
    B: SelectableBackend,
    RNG: CryptoRng,
    S: Step<C, Left = (), Right = ()>,
    V: InternalCircuitVisitor<C>,
{
    app.capture_internal_circuits_seeded(rng, step, witness, visitor)
}
