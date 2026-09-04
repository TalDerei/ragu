mod common;

use common::{arb_sparse_poly, check_sparse_commitment, check_sparse_operations};
use proptest::prelude::*;
use ragu_acceleration::AcceleratedBackend;
use ragu_arithmetic::{
    Cycle,
    pasta_curves::{pallas, vesta},
};
use ragu_pasta::Pasta;
use ragu_testing::strategies::prime_field_element;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn accelerated_pallas_sparse_operations_match_reference_and_canonical(
        lhs in arb_sparse_poly::<pallas::Scalar>(),
        rhs in arb_sparse_poly::<pallas::Scalar>(),
        point in prime_field_element(),
    ) {
        check_sparse_operations::<_, AcceleratedBackend>(lhs, rhs, point)?;
    }

    #[test]
    fn accelerated_vesta_sparse_operations_match_reference_and_canonical(
        lhs in arb_sparse_poly::<vesta::Scalar>(),
        rhs in arb_sparse_poly::<vesta::Scalar>(),
        point in prime_field_element(),
    ) {
        check_sparse_operations::<_, AcceleratedBackend>(lhs, rhs, point)?;
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn accelerated_pallas_sparse_commitment_matches_reference_and_canonical(
        poly in arb_sparse_poly::<pallas::Scalar>(),
    ) {
        check_sparse_commitment::<_, pallas::Affine, _, AcceleratedBackend>(
            poly,
            Pasta::nested_generators(Pasta::baked()),
        )?;
    }

    #[test]
    fn accelerated_vesta_sparse_commitment_matches_reference_and_canonical(
        poly in arb_sparse_poly::<vesta::Scalar>(),
    ) {
        check_sparse_commitment::<_, vesta::Affine, _, AcceleratedBackend>(
            poly,
            Pasta::host_generators(Pasta::baked()),
        )?;
    }
}
