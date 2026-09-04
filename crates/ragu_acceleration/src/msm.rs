//! Accelerated multiscalar multiplication dispatch.

extern crate alloc;

use alloc::vec::Vec;

use ragu_arithmetic::CurveAffine;
use ragu_backend::Backend;

use crate::AcceleratedBackend;

impl Backend for AcceleratedBackend {
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
        let coeffs: Vec<_> = coeffs.into_iter().copied().collect();
        let bases: Vec<_> = bases.into_iter().copied().collect();
        accelerated_msm(&coeffs, &bases)
    }
}

/// Computes the MSM with Zakura's signed-Booth multiexp.
///
/// `zakura-halo2-proofs` depends on the same `zakura-pasta-curves` package as
/// Ragu, so the curve types (and the [`CurveAffine`] trait itself) unify and
/// the call needs no conversion. The implementation is variable-time and uses
/// threads only when `maybe-rayon` threading is enabled (via the `multicore`
/// feature) and beneficial.
///
/// Unequal input lengths violate [`Backend::msm`]'s
/// contract. The reference implementation zips its inputs and so truncates the
/// longer one; this does the same, so the two backends agree even on inputs
/// the contract excludes rather than diverging between a panic and a result.
fn accelerated_msm<C: CurveAffine>(coeffs: &[C::Scalar], bases: &[C]) -> C::Curve {
    #[cfg(test)]
    tests::record_native_msm_call();

    let len = coeffs.len().min(bases.len());
    halo2_proofs::arithmetic::best_multiexp(&coeffs[..len], &bases[..len])
}

#[cfg(test)]
mod tests {
    use core::sync::atomic::{AtomicUsize, Ordering};

    use ragu_arithmetic::{
        group::{Curve, Group},
        pasta_curves::pallas,
    };

    use super::*;

    static NATIVE_MSM_CALLS: AtomicUsize = AtomicUsize::new(0);

    pub(super) fn record_native_msm_call() {
        NATIVE_MSM_CALLS.fetch_add(1, Ordering::Relaxed);
    }

    #[test]
    fn accelerated_backend_dispatch_reaches_native_msm() {
        let scalar = pallas::Scalar::from(2);
        let base = pallas::Point::generator().to_affine();
        let calls_before = NATIVE_MSM_CALLS.load(Ordering::Relaxed);

        let _ = <AcceleratedBackend as Backend>::msm([&scalar], [&base]);

        assert_eq!(
            NATIVE_MSM_CALLS.load(Ordering::Relaxed),
            calls_before + 1,
            "AcceleratedBackend::msm did not dispatch to the native implementation",
        );
    }
}
