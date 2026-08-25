//! Semantic proof comparison for backend-equivalence tests.

#[cfg(feature = "unstable-fuzzing")]
use blake2b_simd::{Params, State};
#[cfg(feature = "unstable-fuzzing")]
use ragu_arithmetic::{CurveAffine, ff::PrimeField};
use ragu_arithmetic::{Cycle, ff::Field};
use ragu_circuits::polynomials::{Rank, sparse::Polynomial};

use super::Proof;
use crate::internal::{native, nested};

fn polynomial_eq<F: Field, R: Rank>(left: &Polynomial<F, R>, right: &Polynomial<F, R>) -> bool {
    left.iter_coeffs().eq(right.iter_coeffs())
}

impl<C: Cycle, R: Rank> Proof<C, R> {
    /// Returns the first category in which two proofs differ semantically.
    ///
    /// The exhaustive pattern makes additions to [`Proof`] fail to compile
    /// until this comparison is reviewed. Polynomials are compared by their
    /// coefficient streams rather than their sparse storage layout.
    pub(crate) fn test_mismatch(&self, other: &Self) -> Option<&'static str> {
        let Self {
            bridge_alpha: _,
            circuit_id: _,
            left_header: _,
            right_header: _,
            native_application_rx: _,
            native_preamble_rx: _,
            native_inner_error_rx: _,
            native_outer_error_rx: _,
            native_a_poly: _,
            native_b_poly: _,
            native_query_rx: _,
            native_registry_xy_poly: _,
            native_eval_rx: _,
            native_p_poly: _,
            native_hashes_1_rx: _,
            native_hashes_2_rx: _,
            native_inner_collapse_rx: _,
            native_outer_collapse_rx: _,
            native_compute_v_rx: _,
            bridge_preamble_rx: _,
            bridge_s_prime_rx: _,
            bridge_inner_error_rx: _,
            bridge_f_rx: _,
            bridge_outer_error_rx: _,
            bridge_ab_rx: _,
            bridge_query_rx: _,
            bridge_eval_rx: _,
            nested_endoscaling_step_rxs: _,
            nested_endoscalar_rx: _,
            nested_points_rx: _,
            nested_endoscaling_step_commitments: _,
            nested_endoscalar_commitment: _,
            nested_points_commitment: _,
            w: _,
            y: _,
            z: _,
            mu: _,
            nu: _,
            mu_prime: _,
            nu_prime: _,
            x: _,
            alpha: _,
            u: _,
            pre_beta: _,
            native_application_commitment: _,
            native_preamble_commitment: _,
            native_inner_error_commitment: _,
            native_outer_error_commitment: _,
            native_a_commitment: _,
            native_b_commitment: _,
            native_query_commitment: _,
            native_registry_xy_commitment: _,
            native_eval_commitment: _,
            native_p_commitment: _,
            native_hashes_1_commitment: _,
            native_hashes_2_commitment: _,
            native_inner_collapse_commitment: _,
            native_outer_collapse_commitment: _,
            native_compute_v_commitment: _,
            bridge_preamble_commitment: _,
            bridge_s_prime_commitment: _,
            bridge_inner_error_commitment: _,
            bridge_f_commitment: _,
            bridge_outer_error_commitment: _,
            bridge_ab_commitment: _,
            bridge_query_commitment: _,
            bridge_eval_commitment: _,
            child_left_stage_rx: _,
            child_right_stage_rx: _,
        } = self;

        if self.bridge_alpha != other.bridge_alpha {
            return Some("bridge alpha");
        }
        if self.circuit_id != other.circuit_id {
            return Some("circuit id");
        }
        if self.left_header != other.left_header || self.right_header != other.right_header {
            return Some("headers");
        }

        if native::RxIndex::ALL
            .into_iter()
            .any(|index| !polynomial_eq(&self[index], &other[index]))
        {
            return Some("native rx polynomials");
        }
        if !polynomial_eq(&self.native_a_poly, &other.native_a_poly)
            || !polynomial_eq(&self.native_b_poly, &other.native_b_poly)
        {
            return Some("native ab polynomials");
        }
        if !polynomial_eq(
            &self.native_registry_xy_poly,
            &other.native_registry_xy_poly,
        ) || !polynomial_eq(&self.native_p_poly, &other.native_p_poly)
        {
            return Some("native protocol polynomials");
        }
        if nested::RxIndex::ALL
            .into_iter()
            .any(|index| !polynomial_eq(&self[index], &other[index]))
        {
            return Some("nested polynomials");
        }

        if [
            self.w,
            self.y,
            self.z,
            self.mu,
            self.nu,
            self.mu_prime,
            self.nu_prime,
            self.x,
            self.alpha,
            self.u,
            self.pre_beta,
        ] != [
            other.w,
            other.y,
            other.z,
            other.mu,
            other.nu,
            other.mu_prime,
            other.nu_prime,
            other.x,
            other.alpha,
            other.u,
            other.pre_beta,
        ] {
            return Some("challenges");
        }

        if native::RxIndex::ALL
            .into_iter()
            .any(|index| self.native_rx_commitment(index) != other.native_rx_commitment(index))
        {
            return Some("native rx commitments");
        }
        if self.native_commitment(native::RxComponent::AbA)
            != other.native_commitment(native::RxComponent::AbA)
            || self.native_commitment(native::RxComponent::AbB)
                != other.native_commitment(native::RxComponent::AbB)
        {
            return Some("native ab commitments");
        }
        if self.native_registry_xy_commitment() != other.native_registry_xy_commitment()
            || self.native_p_commitment() != other.native_p_commitment()
        {
            return Some("native protocol commitments");
        }

        if self.nested_endoscaling_step_commitments != other.nested_endoscaling_step_commitments
            || self.nested_endoscalar_commitment != other.nested_endoscalar_commitment
            || self.nested_points_commitment != other.nested_points_commitment
        {
            return Some("nested commitments");
        }
        if [
            self.bridge_preamble_commitment(),
            self.bridge_s_prime_commitment(),
            self.bridge_inner_error_commitment(),
            self.bridge_outer_error_commitment(),
            self.bridge_ab_commitment(),
            self.bridge_query_commitment(),
            self.bridge_f_commitment(),
            self.bridge_eval_commitment(),
        ] != [
            other.bridge_preamble_commitment(),
            other.bridge_s_prime_commitment(),
            other.bridge_inner_error_commitment(),
            other.bridge_outer_error_commitment(),
            other.bridge_ab_commitment(),
            other.bridge_query_commitment(),
            other.bridge_f_commitment(),
            other.bridge_eval_commitment(),
        ] {
            return Some("bridge commitments");
        }

        None
    }
}

#[cfg(feature = "unstable-fuzzing")]
const DIGEST_SIZE: usize = 32;

#[cfg(feature = "unstable-fuzzing")]
struct ProofDigester(State);

#[cfg(feature = "unstable-fuzzing")]
impl ProofDigester {
    fn new() -> Self {
        let mut state = Params::new().hash_length(DIGEST_SIZE).to_state();
        state.update(b"ragu-proof-digest-v1");
        Self(state)
    }

    fn frame(&mut self, bytes: &[u8]) {
        self.0.update(&(bytes.len() as u64).to_le_bytes());
        self.0.update(bytes);
    }

    fn sequence(&mut self, name: &[u8], len: usize) {
        self.frame(name);
        self.0.update(&(len as u64).to_le_bytes());
    }

    fn field<F: PrimeField>(&mut self, name: &[u8], value: &F) {
        self.frame(name);
        self.field_value(value);
    }

    fn field_value<F: PrimeField>(&mut self, value: &F) {
        let repr = value.to_repr();
        self.frame(repr.as_ref());
    }

    fn field_slice<F: PrimeField>(&mut self, name: &[u8], values: &[F]) {
        self.sequence(name, values.len());
        for value in values {
            self.field_value(value);
        }
    }

    fn polynomial<F: PrimeField, R: Rank>(&mut self, poly: &Polynomial<F, R>) {
        self.0.update(&(R::num_coeffs() as u64).to_le_bytes());
        for coeff in poly.iter_coeffs() {
            self.field_value(&coeff);
        }
    }

    fn point<C: CurveAffine>(&mut self, point: &C) {
        let repr = point.to_bytes();
        self.frame(repr.as_ref());
    }

    fn finish(self) -> [u8; DIGEST_SIZE] {
        let hash = self.0.finalize();
        let mut digest = [0; DIGEST_SIZE];
        digest.copy_from_slice(hash.as_bytes());
        digest
    }
}

#[cfg(feature = "unstable-fuzzing")]
impl<C: Cycle, R: Rank> Proof<C, R> {
    /// A digest of every field of the proof for committed backend goldens.
    ///
    /// This is not a stable format or part of the public API. It is exposed
    /// only by `unstable-fuzzing`; ordinary backend equivalence uses the
    /// semantic comparison above rather than treating a hash as equality.
    pub fn test_digest(&self) -> [u8; DIGEST_SIZE] {
        let mut digest = ProofDigester::new();

        digest.field(b"bridge_alpha", &self.bridge_alpha);
        digest.frame(b"circuit_id");
        digest
            .0
            .update(&(usize::from(self.circuit_id) as u64).to_le_bytes());
        digest.field_slice(b"left_header", &self.left_header);
        digest.field_slice(b"right_header", &self.right_header);

        digest.sequence(b"native_rx_polynomials", native::RxIndex::ALL.len());
        for index in native::RxIndex::ALL {
            digest.polynomial(&self[index]);
        }
        let native_ab_polynomials = [&self.native_a_poly, &self.native_b_poly];
        digest.sequence(b"native_ab_polynomials", native_ab_polynomials.len());
        for polynomial in native_ab_polynomials {
            digest.polynomial(polynomial);
        }
        let native_protocol_polynomials = [&self.native_registry_xy_poly, &self.native_p_poly];
        digest.sequence(
            b"native_protocol_polynomials",
            native_protocol_polynomials.len(),
        );
        for polynomial in native_protocol_polynomials {
            digest.polynomial(polynomial);
        }

        digest.sequence(b"nested_polynomials", nested::RxIndex::ALL.len());
        for index in nested::RxIndex::ALL {
            digest.polynomial(&self[index]);
        }

        for (name, value) in [
            (b"w".as_slice(), self.w),
            (b"y".as_slice(), self.y),
            (b"z".as_slice(), self.z),
            (b"mu".as_slice(), self.mu),
            (b"nu".as_slice(), self.nu),
            (b"mu_prime".as_slice(), self.mu_prime),
            (b"nu_prime".as_slice(), self.nu_prime),
            (b"x".as_slice(), self.x),
            (b"alpha".as_slice(), self.alpha),
            (b"u".as_slice(), self.u),
            (b"pre_beta".as_slice(), self.pre_beta),
        ] {
            digest.field(name, &value);
        }

        digest.sequence(b"native_rx_commitments", native::RxIndex::ALL.len());
        for index in native::RxIndex::ALL {
            digest.point(&self.native_rx_commitment(index));
        }
        let native_ab_commitments = [
            self.native_commitment(native::RxComponent::AbA),
            self.native_commitment(native::RxComponent::AbB),
        ];
        digest.sequence(b"native_ab_commitments", native_ab_commitments.len());
        for commitment in &native_ab_commitments {
            digest.point(commitment);
        }
        let native_protocol_commitments = [
            self.native_registry_xy_commitment(),
            self.native_p_commitment(),
        ];
        digest.sequence(
            b"native_protocol_commitments",
            native_protocol_commitments.len(),
        );
        for commitment in &native_protocol_commitments {
            digest.point(commitment);
        }

        digest.sequence(
            b"nested_endoscaling_step_commitments",
            self.nested_endoscaling_step_commitments.len(),
        );
        for commitment in &self.nested_endoscaling_step_commitments {
            digest.point(&commitment.0);
        }
        let nested_stage_commitments = [
            self.nested_endoscalar_commitment(),
            self.nested_points_commitment(),
        ];
        digest.sequence(b"nested_stage_commitments", nested_stage_commitments.len());
        for commitment in &nested_stage_commitments {
            digest.point(commitment);
        }
        let bridge_commitments = [
            self.bridge_preamble_commitment(),
            self.bridge_s_prime_commitment(),
            self.bridge_inner_error_commitment(),
            self.bridge_outer_error_commitment(),
            self.bridge_ab_commitment(),
            self.bridge_query_commitment(),
            self.bridge_f_commitment(),
            self.bridge_eval_commitment(),
        ];
        digest.sequence(b"bridge_commitments", bridge_commitments.len());
        for commitment in &bridge_commitments {
            digest.point(commitment);
        }

        digest.finish()
    }
}
