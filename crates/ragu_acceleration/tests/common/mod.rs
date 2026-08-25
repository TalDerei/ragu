//! Differential checks shared by the equivalence tests and by the oracle
//! liveness test. Every check compares the canonical implementation, the
//! reference backend, and a backend under test `A`, and returns `Err` rather
//! than panicking so that a backend which *should* fail can be shown to.
#![allow(dead_code)]

use proptest::{prelude::*, test_runner::TestCaseResult};
use ragu_arithmetic::{
    CurveAffine, DeferredField, FixedGenerators,
    ff::PrimeField,
    group::{Curve, Group},
};
use ragu_backend::{Backend, ReferenceBackend};
use ragu_circuits::polynomials::{ProductionRank, Rank, TestRank, sparse::Polynomial};
use ragu_testing::strategies::{bounded_edge_usize, prime_field_element};

/// Sizes at which the accelerated MSM changes algorithm
/// (`qa/backend/transitions/msm.txt`).
pub fn msm_transition_sizes() -> Vec<usize> {
    include_str!("../../../../qa/backend/transitions/msm.txt")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.parse::<usize>().expect("transition size"))
        .collect()
}

pub fn arb_msm_size() -> impl Strategy<Value = usize> {
    let window_boundaries = (0..=ProductionRank::RANK, -1i8..=1).prop_map(|(log_size, offset)| {
        let boundary = 1usize << log_size;
        match offset {
            -1 => boundary - 1,
            0 => boundary,
            1 => (boundary + 1).min(ProductionRank::num_coeffs()),
            _ => unreachable!("the generated offset is in -1..=1"),
        }
    });

    prop_oneof![
        bounded_edge_usize(TestRank::num_coeffs()),
        window_boundaries,
    ]
}

pub fn arb_msm_terms<F>() -> impl Strategy<Value = Vec<(F, F)>>
where
    F: PrimeField + From<u64> + 'static,
{
    arb_msm_size().prop_flat_map(|size| {
        let independent = proptest::collection::vec(
            (prime_field_element::<F>(), prime_field_element::<F>()),
            size,
        );
        let repeated = (
            proptest::collection::vec(prime_field_element::<F>(), size),
            prime_field_element::<F>(),
        )
            .prop_map(|(scalars, base)| scalars.into_iter().map(|scalar| (scalar, base)).collect());
        let repeated_with_inverses = (
            proptest::collection::vec((prime_field_element::<F>(), any::<bool>()), size),
            prime_field_element::<F>(),
        )
            .prop_map(|(terms, base)| {
                terms
                    .into_iter()
                    .map(|(scalar, negate)| (scalar, if negate { -base } else { base }))
                    .collect()
            });
        let identity_bases =
            proptest::collection::vec(prime_field_element::<F>(), size).prop_map(|scalars| {
                scalars
                    .into_iter()
                    .map(|scalar| (scalar, F::ZERO))
                    .collect()
            });
        let zero_scalars = proptest::collection::vec(prime_field_element::<F>(), size)
            .prop_map(|bases| bases.into_iter().map(|base| (F::ZERO, base)).collect());

        prop_oneof![
            independent,
            repeated,
            repeated_with_inverses,
            identity_bases,
            zero_scalars,
        ]
    })
}

/// Deterministic MSM terms of a given size, for the transition sweep.
pub fn deterministic_terms<F: From<u64>>(size: usize) -> Vec<(F, F)> {
    (0..size)
        .map(|index| {
            let index = index as u64;
            (F::from(index + 1), F::from(index.wrapping_mul(17) + 3))
        })
        .collect()
}

/// `A::msm` and the reference must both equal the canonical MSM.
pub fn check_msm<C: CurveAffine, A: Backend>(
    terms: Vec<(C::ScalarExt, C::ScalarExt)>,
) -> TestCaseResult {
    let generator = C::CurveExt::generator();
    let (scalars, bases): (Vec<_>, Vec<_>) = terms
        .into_iter()
        .map(|(scalar, base_scalar)| (scalar, (generator * base_scalar).to_affine()))
        .unzip();

    let canonical = ragu_arithmetic::msm(scalars.iter(), bases.iter());
    let reference = ReferenceBackend::msm(scalars.iter(), bases.iter());
    let under_test = A::msm(scalars.iter(), bases.iter());

    prop_assert_eq!(reference, canonical);
    prop_assert_eq!(under_test, canonical);

    Ok(())
}

/// The transition sweep: both sides of every algorithm boundary plus the
/// production size, on one curve.
pub fn check_msm_transitions<C: CurveAffine, A: Backend>() -> TestCaseResult
where
    C::ScalarExt: From<u64>,
{
    let sizes = msm_transition_sizes()
        .into_iter()
        .flat_map(|boundary| [boundary - 1, boundary])
        .chain(core::iter::once(ProductionRank::num_coeffs()));
    for size in sizes {
        check_msm::<C, A>(deterministic_terms(size))?;
    }
    Ok(())
}

pub fn arb_sparse_poly<F>() -> BoxedStrategy<Polynomial<F, TestRank>>
where
    F: PrimeField + From<u64> + 'static,
{
    let size = bounded_edge_usize(TestRank::num_coeffs());

    size.prop_flat_map(|size| {
        proptest::collection::vec(
            prop_oneof![
                6 => Just(F::ZERO),
                1 => Just(F::ONE),
                8 => prime_field_element(),
            ],
            size,
        )
    })
    .prop_map(Polynomial::from_coeffs)
    .boxed()
}

/// `A::sparse_eval` and `A::sparse_revdot` (and the reference) must equal the
/// canonical polynomial operations.
pub fn check_sparse_operations<F, A>(
    lhs: Polynomial<F, TestRank>,
    rhs: Polynomial<F, TestRank>,
    point: F,
) -> TestCaseResult
where
    F: DeferredField,
    A: Backend,
{
    let canonical_lhs_eval = lhs.eval(point);
    let canonical_rhs_eval = rhs.eval(point);

    prop_assert_eq!(
        ReferenceBackend::sparse_eval(&lhs, point),
        canonical_lhs_eval
    );
    prop_assert_eq!(A::sparse_eval(&lhs, point), canonical_lhs_eval);
    prop_assert_eq!(
        ReferenceBackend::sparse_eval(&rhs, point),
        canonical_rhs_eval
    );
    prop_assert_eq!(A::sparse_eval(&rhs, point), canonical_rhs_eval);

    let canonical_revdot = lhs.revdot(&rhs);
    prop_assert_eq!(
        ReferenceBackend::sparse_revdot(&lhs, &rhs),
        canonical_revdot
    );
    prop_assert_eq!(A::sparse_revdot(&lhs, &rhs), canonical_revdot);

    Ok(())
}

/// `A::sparse_commit` and `A::sparse_commit_to_affine` (and the reference)
/// must equal the canonical commitment.
pub fn check_sparse_commitment<F, C, G, A>(
    poly: Polynomial<F, TestRank>,
    generators: &G,
) -> TestCaseResult
where
    F: PrimeField,
    C: CurveAffine<ScalarExt = F>,
    G: FixedGenerators<C>,
    A: Backend,
{
    let canonical = poly.commit(generators);

    prop_assert_eq!(
        ReferenceBackend::sparse_commit(&poly, generators),
        canonical
    );
    prop_assert_eq!(A::sparse_commit(&poly, generators), canonical);
    prop_assert_eq!(
        ReferenceBackend::sparse_commit_to_affine(&poly, generators),
        canonical.to_affine(),
    );
    prop_assert_eq!(
        A::sparse_commit_to_affine(&poly, generators),
        canonical.to_affine()
    );

    Ok(())
}
