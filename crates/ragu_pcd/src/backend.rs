//! Sealed selection of the computational backend.
//!
//! This is the only file in `ragu_pcd` that names `ragu_acceleration`: the
//! sealed mapping below decides which backends an application may select and
//! which kernels the verifier consults for each of them.

use ragu_backend::Backend;

mod sealed {
    use ragu_acceleration::{AcceleratedBackend, AcceleratedProver};
    use ragu_backend::{Backend, ReferenceBackend};

    pub trait Sealed {
        type Verifier: Backend;
    }

    impl Sealed for ReferenceBackend {
        type Verifier = ReferenceBackend;
    }

    impl Sealed for AcceleratedBackend {
        type Verifier = AcceleratedBackend;
    }

    impl Sealed for AcceleratedProver {
        type Verifier = ReferenceBackend;
    }
}

/// A Ragu-owned computational backend.
///
/// This trait is sealed: applications may select one of Ragu's supported
/// implementations, but cannot provide their own backend implementation.
/// Each selectable backend also fixes [`Verifier`](Self::Verifier), the
/// backend whose kernels [`Application::verify`](crate::Application::verify)
/// consults, so accelerating verification is an explicit choice rather
/// than a consequence of accelerating proving.
pub trait SelectableBackend: Backend + sealed::Sealed {
    /// The backend whose kernels the verifier consults.
    ///
    /// `ReferenceBackend` and `AcceleratedBackend` verify with their own
    /// kernels; `AcceleratedProver` proves with the accelerated kernels
    /// and verifies with the reference ones.
    type Verifier: Backend;
}

impl<T: Backend + sealed::Sealed> SelectableBackend for T {
    type Verifier = <T as sealed::Sealed>::Verifier;
}

#[cfg(test)]
pub(crate) mod tracking {
    use core::sync::atomic::{AtomicUsize, Ordering};

    use ragu_backend::Backend;

    use super::sealed;

    static MSM_CALLS: AtomicUsize = AtomicUsize::new(0);

    /// Test backend that records whether PCD dispatch reaches `Backend::msm`.
    #[derive(Clone, Copy, Debug, Default)]
    pub(crate) struct TrackingBackend;

    impl TrackingBackend {
        pub(crate) fn reset_msm_calls() {
            MSM_CALLS.store(0, Ordering::Relaxed);
        }

        pub(crate) fn msm_calls() -> usize {
            MSM_CALLS.load(Ordering::Relaxed)
        }
    }

    impl Backend for TrackingBackend {
        fn msm<
            'a,
            C: ragu_arithmetic::CurveAffine,
            A: IntoIterator<Item = &'a C::Scalar>,
            Bases: IntoIterator<Item = &'a C>,
        >(
            coeffs: A,
            bases: Bases,
        ) -> C::Curve
        where
            Bases::IntoIter: Clone + Sync,
        {
            MSM_CALLS.fetch_add(1, Ordering::Relaxed);
            ragu_backend::ReferenceBackend::msm(coeffs, bases)
        }
    }

    impl sealed::Sealed for TrackingBackend {
        type Verifier = Self;
    }
}
