//! Verifier-consulted kernels.
//!
//! The [`Backend`](ragu_backend::Backend) trait has a single set of methods,
//! and the prover uses all of them. Four of them — `sparse_eval`,
//! `sparse_revdot`, `registry_circuit_y`, and `registry_wxy` — are *also*
//! what `ragu_pcd`'s verifier uses to compute the left-hand side of its
//! acceptance comparisons, whenever the selected backend's `Verifier` is the
//! accelerated one (`AcceleratedBackend`, but not `AcceleratedProver`). An
//! override of any of those four is shared by the prover and the verifier;
//! it is implemented in this module and reached from the `Backend` impl in
//! the crate root by delegation, so the code that can influence an
//! acceptance decision is confined to one place. Code here is held to a
//! stricter bar than prover-only overrides: deterministic in its arguments,
//! no control flow that depends on field or point values, mutation-tested,
//! and differentially fuzzed.
//!
//! Nothing is overridden here yet; [`AcceleratedBackend`](crate::AcceleratedBackend)
//! verifies with the reference kernels until the first override lands.
