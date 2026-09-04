mod common;

use common::{arb_msm_terms, check_msm, check_msm_transitions};
use proptest::{prelude::*, test_runner::TestCaseResult};
use ragu_acceleration::AcceleratedBackend;
use ragu_arithmetic::pasta_curves::{pallas, vesta};

#[test]
fn exact_algorithm_boundaries_match_canonical_msm() -> TestCaseResult {
    // Sizes at which the canonical MSM changes its Booth-window width.
    // Keep them deterministic: the proptest strategy is power-of-two biased and
    // cannot generate most of these transition points.
    check_msm_transitions::<pallas::Affine, AcceleratedBackend>()?;
    check_msm_transitions::<vesta::Affine, AcceleratedBackend>()?;
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn accelerated_pallas_msm_matches_reference_and_canonical(
        terms in arb_msm_terms::<pallas::Scalar>(),
    ) {
        check_msm::<pallas::Affine, AcceleratedBackend>(terms)?;
    }

    #[test]
    fn accelerated_vesta_msm_matches_reference_and_canonical(
        terms in arb_msm_terms::<vesta::Scalar>(),
    ) {
        check_msm::<vesta::Affine, AcceleratedBackend>(terms)?;
    }
}
