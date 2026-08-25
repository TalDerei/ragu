//! # `ragu_backend`
//!
//! Computational backend interfaces for Ragu.

#![no_std]
#![deny(missing_docs)]
#![forbid(unsafe_code)]

use core::fmt::Debug;

use ragu_arithmetic::{
    CurveAffine, DeferredField, FixedGenerators,
    ff::{Field, PrimeField},
};
use ragu_circuits::{
    polynomials::{Rank, sparse},
    registry::{CircuitIndex, Registry, RegistryAt},
};

/// A statically dispatched implementation of Ragu's computational operations.
///
/// Every method has a correctness-first default that delegates to the
/// canonical implementation in `ragu_arithmetic` or `ragu_circuits`.
/// Implementations may override individual methods, but an override must be
/// observationally identical to the default. Canonical circuit and protocol
/// data is constructed before it reaches these methods; a backend only changes
/// how the requested computation is performed. Implementing this low-level
/// trait does not make a downstream type selectable by `ragu_pcd`; application
/// execution is restricted to Ragu-owned backends.
///
/// # Contract
///
/// **Equality.** An override must return a value equal to the default's under
/// the canonical comparison for its type: field elements by their canonical
/// representation, affine points by coordinates, projective points by group
/// equality (their $(X : Y : Z)$ representation is unspecified, and callers
/// normalize before serializing, hashing, or absorbing them), sparse
/// polynomials by their coefficient sequence (their block layout is
/// unspecified), and batch outputs positionally at the documented indices.
///
/// **Schedule freedom.** Ragu's arithmetic is exact, and [`DeferredField`]
/// accumulators are integer sums with headroom, so an override may
/// re-associate, partition, vectorize, or parallelize any field sum, product
/// accumulation, or group sum, and may reuse or cache derived data such as
/// tables and precomputed powers, provided the result is a deterministic
/// function of the arguments.
///
/// **Schedule constraints.** An override must not consume randomness, read
/// time or thread identity, or depend on ambient mutable state; no method of
/// this trait takes a random number generator or a transcript. Output
/// positions are part of a method's specification because callers feed them
/// into stage witnesses and the transcript in that order: compute in any
/// order, write to the documented index.
///
/// **Preconditions.** Shape and length preconditions are validated by the
/// callers before dispatch. Overrides may assume them and must not add checks
/// that change behavior on valid input.
///
/// # What a backend never decides
///
/// A backend performs computations whose specification is a pure function of
/// its arguments and whose canonical implementation already exists. The
/// following stay in canonical code and are never routed through a backend,
/// because a backend that could influence them could change what a proof
/// *means* rather than how fast it is computed: sampling of randomness and the
/// order in which it is consumed; the Fiat-Shamir transcript (what is absorbed,
/// in what order, and how challenges are squeezed and lifted); circuit
/// synthesis, witness allocation, trace assembly, and floor planning; the
/// registry digest and its binding semantics; the structure and serialization
/// of proofs; and every verifier decision, which is a canonical comparison of
/// backend-computed values.
///
/// # Verifier-consulted kernels
///
/// `ragu_pcd`'s verifier consults [`sparse_eval`](Self::sparse_eval),
/// [`sparse_revdot`](Self::sparse_revdot),
/// [`registry_circuit_y`](Self::registry_circuit_y), and
/// [`registry_wxy`](Self::registry_wxy) of the backend it is configured to
/// verify with. Differential testing turns a *buggy* override of these kernels
/// into a completeness failure, since a wrong value equals the canonical one
/// on a forged proof only by accident; it cannot rule out an override written
/// to return a chosen value on a chosen input. Reviewing or formally verifying
/// the override is the only closure for that case, which is why applications
/// choose explicitly whether verification uses accelerated kernels.
///
/// Backends are currently selected by type and cannot carry per-application
/// state. If implementations need device handles or caches, Ragu can store the
/// selected backend as a value while retaining static dispatch.
pub trait Backend: Clone + Copy + Debug + Default + Send + Sync + 'static {
    /// Evaluates a sparse polynomial at `point`.
    ///
    /// # Correctness
    ///
    /// Overrides must match [`sparse::Polynomial::eval`] exactly.
    fn sparse_eval<F: Field, R: Rank>(poly: &sparse::Polynomial<F, R>, point: F) -> F {
        poly.eval(point)
    }

    /// Computes the reverse inner product of two sparse polynomials.
    ///
    /// # Correctness
    ///
    /// Overrides must match [`sparse::Polynomial::revdot`] exactly.
    fn sparse_revdot<F: DeferredField, R: Rank>(
        lhs: &sparse::Polynomial<F, R>,
        rhs: &sparse::Polynomial<F, R>,
    ) -> F {
        lhs.revdot(rhs)
    }

    /// Commits to a sparse polynomial in projective form.
    ///
    /// The correctness-first implementation dispatches its MSM through
    /// [`Backend::msm`], so overriding MSM also accelerates polynomial
    /// commitments.
    ///
    /// # Correctness
    ///
    /// Overrides must match [`sparse::Polynomial::commit`] exactly.
    fn sparse_commit<F: Field, C: CurveAffine<ScalarExt = F>, R: Rank, G: FixedGenerators<C>>(
        poly: &sparse::Polynomial<F, R>,
        generators: &G,
    ) -> C::Curve {
        assert!(generators.g().len() >= R::num_coeffs());
        let bases = generators.g();

        Self::msm(
            poly.iter_stored_coeffs()
                .map(|(_, coefficient)| coefficient),
            poly.iter_stored_coeffs().map(|(index, _)| &bases[index]),
        )
    }

    /// Commits to a sparse polynomial and normalizes the result to affine.
    ///
    /// # Correctness
    ///
    /// Overrides must match [`sparse::Polynomial::commit_to_affine`] exactly.
    fn sparse_commit_to_affine<
        F: Field,
        C: CurveAffine<ScalarExt = F>,
        R: Rank,
        G: FixedGenerators<C>,
    >(
        poly: &sparse::Polynomial<F, R>,
        generators: &G,
    ) -> C {
        Self::sparse_commit(poly, generators).into()
    }

    /// Computes the registry restriction $m(W, x, y)$.
    fn registry_xy<F: PrimeField, R: Rank>(
        registry: &Registry<'_, F, R>,
        x: F,
        y: F,
    ) -> sparse::Polynomial<F, R> {
        registry.xy(x, y)
    }

    /// Computes the circuit restriction $s_i(X, y)$ selected by `circuit`.
    fn registry_circuit_y<F: PrimeField, R: Rank>(
        registry: &Registry<'_, F, R>,
        circuit: CircuitIndex,
        y: F,
    ) -> sparse::Polynomial<F, R> {
        registry.circuit_y(circuit, y)
    }

    /// Computes the registry restriction $m(w, x, Y)$.
    fn registry_at_x<F: PrimeField, R: Rank>(
        registry: &RegistryAt<'_, F, R>,
        x: F,
    ) -> sparse::Polynomial<F, R> {
        registry.x(x)
    }

    /// Computes the registry restriction $m(w, X, y)$.
    fn registry_at_y<F: PrimeField, R: Rank>(
        registry: &RegistryAt<'_, F, R>,
        y: F,
    ) -> sparse::Polynomial<F, R> {
        registry.y(y)
    }

    /// Evaluates the registry polynomial at $(w, x, y)$.
    fn registry_wxy<F: PrimeField, R: Rank>(registry: &Registry<'_, F, R>, w: F, x: F, y: F) -> F {
        registry.wxy(w, x, y)
    }

    /// Computes the multiscalar multiplication
    /// $\langle \mathbf{a}, \mathbf{G} \rangle$.
    ///
    /// # Correctness
    ///
    /// The caller must ensure that `coeffs` and `bases` yield the same number
    /// of elements. Overrides must match [`ragu_arithmetic::msm`] exactly.
    fn msm<
        'a,
        C: CurveAffine,
        A: IntoIterator<Item = &'a C::Scalar>,
        Bases: IntoIterator<Item = &'a C>,
    >(
        coeffs: A,
        bases: Bases,
    ) -> C::Curve
    where
        Bases::IntoIter: Clone + Sync,
    {
        ragu_arithmetic::msm(coeffs, bases)
    }
}

/// The correctness-first backend used by default throughout Ragu.
#[derive(Clone, Copy, Debug, Default)]
pub struct ReferenceBackend;

impl Backend for ReferenceBackend {}
