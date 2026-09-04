//! The differential harness must be able to fail.
//!
//! An oracle that cannot fire looks exactly like an oracle that found no bug,
//! so this test plants one: a backend that is correct everywhere except at one
//! MSM size and one polynomial shape. The same checks the accelerated backend
//! passes must reject it, and must accept it away from the planted sizes, so
//! a rejection is specific rather than a harness error.

mod common;

use common::{check_msm, check_msm_transitions, check_sparse_operations, deterministic_terms};
use ragu_acceleration::AcceleratedBackend;
use ragu_arithmetic::{
    CurveAffine,
    ff::Field,
    group::Group,
    pasta_curves::{pallas, vesta},
};
use ragu_backend::{Backend, ReferenceBackend};
use ragu_circuits::polynomials::{Rank, TestRank, sparse::Polynomial};

/// A transition size: the sweep must catch a bug that lives only there.
const SENTINEL_MSM_SIZE: usize = 8104;
/// A stored-coefficient count the sparse strategy generates.
const SENTINEL_POLY_SIZE: usize = 17;

#[derive(Clone, Copy, Debug, Default)]
struct SentinelBackend;

impl Backend for SentinelBackend {
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
        let bases = bases.into_iter();
        let len = bases.clone().count();
        let result = ReferenceBackend::msm(coeffs, bases);
        if len == SENTINEL_MSM_SIZE {
            result + C::Curve::generator()
        } else {
            result
        }
    }

    fn sparse_eval<F: Field, R: Rank>(poly: &Polynomial<F, R>, point: F) -> F {
        let stored = poly.iter_stored_coeffs().count();
        let value = poly.eval(point);
        if stored == SENTINEL_POLY_SIZE {
            value + F::ONE
        } else {
            value
        }
    }
}

#[test]
fn msm_check_rejects_the_sentinel_only_at_its_size() {
    let at = deterministic_terms::<pallas::Scalar>(SENTINEL_MSM_SIZE);
    let near = deterministic_terms::<pallas::Scalar>(SENTINEL_MSM_SIZE - 1);

    assert!(check_msm::<pallas::Affine, AcceleratedBackend>(at.clone()).is_ok());
    assert!(check_msm::<pallas::Affine, SentinelBackend>(at).is_err());
    assert!(check_msm::<pallas::Affine, SentinelBackend>(near).is_ok());
}

#[test]
fn transition_sweep_rejects_the_sentinel() {
    assert!(
        common::msm_transition_sizes().contains(&SENTINEL_MSM_SIZE),
        "the sentinel must sit on a listed transition for this test to mean anything"
    );
    assert!(check_msm_transitions::<pallas::Affine, AcceleratedBackend>().is_ok());
    assert!(check_msm_transitions::<vesta::Affine, AcceleratedBackend>().is_ok());
    assert!(check_msm_transitions::<pallas::Affine, SentinelBackend>().is_err());
    assert!(check_msm_transitions::<vesta::Affine, SentinelBackend>().is_err());
}

#[test]
fn sparse_check_rejects_the_sentinel_only_at_its_shape() {
    let poly = |stored: usize| {
        Polynomial::<pallas::Scalar, TestRank>::from_coeffs(
            (0..stored)
                .map(|i| pallas::Scalar::from(i as u64 + 1))
                .collect(),
        )
    };
    let point = pallas::Scalar::from(5);

    assert!(
        check_sparse_operations::<_, AcceleratedBackend>(poly(SENTINEL_POLY_SIZE), poly(3), point)
            .is_ok()
    );
    assert!(
        check_sparse_operations::<_, SentinelBackend>(poly(SENTINEL_POLY_SIZE), poly(3), point)
            .is_err()
    );
    assert!(
        check_sparse_operations::<_, SentinelBackend>(poly(SENTINEL_POLY_SIZE + 1), poly(3), point)
            .is_ok()
    );
}
