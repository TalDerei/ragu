//! Commit to the evaluations of every queried polynomial at $u$.
//!
//! This sets the native `eval` stage containing the claimed evaluations at $u$
//! of every element that was also queried in the `query` stage. The evaluation
//! $f(u)$ is derived from the aforementioned evaluations.

use ff::Field;
use ragu_arithmetic::{Cycle, par_join};
use ragu_circuits::{polynomials::Rank, staging::StageExt};
use ragu_core::{Result, drivers::Driver, maybe::Maybe};
use ragu_primitives::Element;
use rand::CryptoRng;

use super::{NativeSPrime, RegistryWy};
use crate::{Application, Proof, internal::native, proof::ProofBuilder};

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    pub(super) fn compute_eval<'dr, D, RNG: CryptoRng>(
        &self,
        rng: &mut RNG,
        u: &Element<'dr, D>,
        left: &Proof<C, R>,
        right: &Proof<C, R>,
        s_prime: &NativeSPrime<C, R>,
        registry_wy: &RegistryWy<C, R>,
        builder: &mut ProofBuilder<'_, C, R>,
    ) -> Result<native::stages::eval::Witness<C::CircuitField>>
    where
        D: Driver<'dr, F = C::CircuitField>,
    {
        let u = *u.value().take();

        // ProofBuilder contains OnceCell fields and is therefore !Sync.
        // Extract shared references to the already-set polynomials so the
        // closures below capture &Polynomial (which is Sync) rather than
        // &ProofBuilder.
        let native_a_poly = builder.native_a_poly();
        let native_b_poly = builder.native_b_poly();
        let native_registry_xy_poly = builder.native_registry_xy_poly();

        // Evaluate left/right child witnesses concurrently with the
        // current-step polynomial evaluations at u.
        let (left_witness, right_witness, current) = par_join!(
            || native::stages::eval::ChildEvaluationsWitness::from_proof(left, u),
            || native::stages::eval::ChildEvaluationsWitness::from_proof(right, u),
            || native::stages::eval::CurrentStepWitness {
                // TODO: registry_wx0_poly, registry_wx1_poly, and
                // registry_wy.poly are each evaluated independently here. A
                // batched evaluation path (analogous to wxy_over_domain) could
                // amortize the per-circuit cost across all three.
                registry_wx0: s_prime.registry_wx0_poly.eval(u),
                registry_wx1: s_prime.registry_wx1_poly.eval(u),
                registry_wy: registry_wy.poly.eval(u),
                a_poly: native_a_poly.eval(u),
                b_poly: native_b_poly.eval(u),
                registry_xy: native_registry_xy_poly.eval(u),
            },
        );
        let eval_witness = native::stages::eval::Witness {
            left: left_witness,
            right: right_witness,
            current,
        };
        let rx = native::stages::eval::Stage::<C, R, HEADER_SIZE>::rx(
            C::CircuitField::random(&mut *rng),
            &eval_witness,
        )?;

        builder.set_native_eval_rx(rx);

        Ok(eval_witness)
    }
}
