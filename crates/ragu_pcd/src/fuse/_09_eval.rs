//! Commit to the evaluations of every queried polynomial at $u$.
//!
//! This sets the native `eval` stage containing the claimed evaluations at $u$
//! of every element that was also queried in the `query` stage. The evaluation
//! $f(u)$ is derived from the aforementioned evaluations.

use ragu_arithmetic::{CryptoRngCore, Cycle, ff::Field};
use ragu_circuits::{
    polynomials::{Rank, sparse},
    staging::StageExt,
};
use ragu_core::{
    Result,
    drivers::{Driver, DriverTypes},
    maybe::{Always, Maybe},
};
use ragu_primitives::{Element, EndoscalarChallenge, GadgetExt, Point};

use super::{NativeSPrime, RegistryWy};
use crate::{
    Application, Proof,
    internal::{native, transcript::Transcript},
    proof::ProofBuilder,
};

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    pub(super) fn compute_eval_witness<'dr, D>(
        &self,
        u: &Element<'dr, D>,
        left: &Proof<C, R>,
        right: &Proof<C, R>,
        s_prime: &NativeSPrime<C, R>,
        registry_wy: &RegistryWy<C, R>,
        builder: &crate::proof::ProofBuilder<'_, C, R>,
    ) -> native::stages::eval::Witness<C::CircuitField>
    where
        D: Driver<'dr, F = C::CircuitField>,
    {
        let u = *u.value().take();

        native::stages::eval::Witness {
            left: native::stages::eval::ChildEvaluationsWitness::from_proof(left, u),
            right: native::stages::eval::ChildEvaluationsWitness::from_proof(right, u),
            current: native::stages::eval::CurrentStepWitness {
                // TODO: the registry evaluations here could _theoretically_ be more
                // efficient if they're computed simultaneously with assistance
                // from the registry itself, rather than individually evaluated for
                // each of these restrictions.
                registry_wx0: s_prime.registry_wx0_poly.eval(u),
                registry_wx1: s_prime.registry_wx1_poly.eval(u),
                registry_wy: registry_wy.poly.eval(u),
                a_poly: builder.native_a_poly().eval(u),
                b_poly: builder.native_b_poly().eval(u),
                registry_xy: builder.native_registry_xy_poly().eval(u),
            },
        }
    }

    pub(super) fn sample_eval_rx<RNG: CryptoRngCore>(
        &self,
        rng: &mut RNG,
        eval_witness: &native::stages::eval::Witness<C::CircuitField>,
    ) -> Result<sparse::Polynomial<C::CircuitField, R>> {
        native::stages::eval::Stage::<C, R, HEADER_SIZE>::rx(
            C::CircuitField::random(&mut *rng),
            eval_witness,
        )
    }

    /// Rejection-samples the eval-stage blinding until the derived `pre_beta`
    /// is an in-range endoscalar challenge.
    ///
    /// This consumes the transcript prefix immediately before the eval
    /// commitment. Each attempt clones that prefix, absorbs a candidate eval
    /// commitment, and squeezes a candidate `pre_beta`; on acceptance, the
    /// matching `eval_rx` and advanced transcript are returned together. The old
    /// prefix is therefore unavailable to callers after sampling, so subsequent
    /// transcript use must explicitly continue from the accepted transcript.
    pub(super) fn sample_pre_beta<'dr, D, RNG>(
        &self,
        rng: &mut RNG,
        dr: &mut D,
        transcript_prefix: Transcript<'dr, D, C::CircuitPoseidon>,
        eval_witness: &native::stages::eval::Witness<C::CircuitField>,
        builder: &ProofBuilder<'_, C, R>,
    ) -> Result<(
        EndoscalarChallenge<'dr, D>,
        sparse::Polynomial<C::CircuitField, R>,
        Transcript<'dr, D, C::CircuitPoseidon>,
    )>
    where
        D: Driver<'dr, F = C::CircuitField, Wire = ()>,
        D: DriverTypes<MaybeKind = Always<()>>,
        RNG: CryptoRngCore,
    {
        // Rejection-sample only the eval-stage blinding. This is the final
        // commitment before `pre_beta`, so changing it gives a fresh challenge
        // without rebuilding the preceding fuse state. The grind lives inside
        // `EndoscalarChallenge::sample`, which (re)derives `pre_beta` from each
        // fresh blinding and retries until it lands in range.
        let (pre_beta, (eval_rx, accepted_transcript)) = EndoscalarChallenge::sample(dr, |dr| {
            let eval_rx = self.sample_eval_rx(rng, eval_witness)?;
            let native_eval_commitment = eval_rx.commit_to_affine(C::host_generators(self.params));
            let bridge_eval_commitment =
                builder.candidate_bridge_eval_commitment(native_eval_commitment)?;

            let mut candidate_transcript = transcript_prefix.clone();
            let eval_commitment = Point::constant(dr, bridge_eval_commitment)?;
            eval_commitment.write(dr, &mut candidate_transcript)?;
            let pre_beta = candidate_transcript.challenge(dr)?;

            Ok((pre_beta, (eval_rx, candidate_transcript)))
        })?;

        Ok((pre_beta, eval_rx, accepted_transcript))
    }
}
