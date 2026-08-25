//! Accelerated multiscalar multiplication dispatch.

use ragu_arithmetic::CurveAffine;

/// Computes the MSM with Zakura's signed-Booth multiexp.
///
/// `zakura-halo2-proofs` depends on the same `zakura-pasta-curves` package as
/// Ragu, so the curve types (and the [`CurveAffine`] trait itself) unify and
/// the call needs no conversion. The implementation is variable-time and uses
/// threads only when `maybe-rayon` threading is enabled (via the `multicore`
/// feature) and beneficial.
///
/// Unequal input lengths violate [`Backend::msm`](ragu_backend::Backend::msm)'s
/// contract. The reference implementation zips its inputs and so truncates the
/// longer one; this does the same, so the two backends agree even on inputs
/// the contract excludes rather than diverging between a panic and a result.
pub(crate) fn accelerated_msm<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    let len = coeffs.len().min(bases.len());
    halo2_proofs::arithmetic::best_multiexp(&coeffs[..len], &bases[..len])
}
