//! # `ragu_acceleration`
//!
//! Optimized implementations of Ragu's computational backend.
//!
//! Overrides live behind opt-in features and fall back to the correctness-first
//! defaults of [`ragu_backend::Backend`] otherwise. Overrides of the kernels
//! that `ragu_pcd`'s verifier consults are implemented in [`verifier`], which
//! carries a stricter review and testing bar than prover-only overrides.

#![no_std]
#![deny(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]

pub mod verifier;

/// Ragu's accelerated computational backend, for proving and verification.
///
/// It currently inherits every correctness-first default from
/// [`ragu_backend::Backend`]. Optimized overrides will be added individually
/// alongside reference-equivalence tests.
///
/// Selecting this backend in `ragu_pcd` also uses its verifier-consulted
/// kernels (see [`verifier`]) when verifying proofs. Select
/// [`AcceleratedProver`] to accelerate proving only.
#[derive(Clone, Copy, Debug, Default)]
pub struct AcceleratedBackend;

/// [`AcceleratedBackend`] for proving, with verification on the reference
/// kernels.
///
/// Computes exactly what [`AcceleratedBackend`] computes; the two differ only
/// in which kernels `ragu_pcd` consults when verifying. Selecting this type
/// keeps every acceptance decision on the canonical code path, at the cost of
/// the verifier-side speedups.
#[derive(Clone, Copy, Debug, Default)]
pub struct AcceleratedProver;

impl ragu_backend::Backend for AcceleratedBackend {}

// `AcceleratedProver` must forward every override to `AcceleratedBackend`,
// one method per override, so the two impl blocks stay comparable and a new
// override cannot be selected for proving while silently missing here.
impl ragu_backend::Backend for AcceleratedProver {}
