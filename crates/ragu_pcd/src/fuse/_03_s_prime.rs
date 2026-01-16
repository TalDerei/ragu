//! Commit to $m(w, x_i, Y)$ polynomials for the child proofs.
//!
//! This creates the [`proof::SPrime`] component of the proof, which commits to
//! the $m(w, x_i, Y)$ polynomials for the $i$th child proof's $x$ challenge.

use arithmetic::Cycle;
use ff::Field;
use ragu_circuits::{polynomials::Rank, staging::StageExt};
use ragu_core::{
    Result,
    drivers::Driver,
    maybe::{Always, Maybe},
};
use ragu_primitives::Element;
use rand::Rng;

use crate::{Application, Proof, circuits::nested, proof};

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    pub(super) fn compute_s_prime<'dr, D, RNG: Rng>(
        &self,
        rng: &mut RNG,
        w: &Element<'dr, D>,
        left: &Proof<C, R>,
        right: &Proof<C, R>,
    ) -> Result<proof::SPrime<C, R>>
    where
        D: Driver<'dr, F = C::CircuitField, MaybeKind = Always<()>>,
    {
        let w = *w.value().take();
        let x0 = left.challenges.x;
        let x1 = right.challenges.x;

        let native_mesh_wx0_poly = self.native_mesh.wx(w, x0);
        let native_mesh_wx0_blind = C::CircuitField::random(&mut *rng);
        let native_mesh_wx0_commitment =
            native_mesh_wx0_poly.commit(C::host_generators(self.params), native_mesh_wx0_blind);
        let native_mesh_wx1_poly = self.native_mesh.wx(w, x1);
        let native_mesh_wx1_blind = C::CircuitField::random(&mut *rng);
        let native_mesh_wx1_commitment =
            native_mesh_wx1_poly.commit(C::host_generators(self.params), native_mesh_wx1_blind);

        let nested_s_prime_witness = nested::stages::s_prime::Witness {
            mesh_wx0: native_mesh_wx0_commitment,
            mesh_wx1: native_mesh_wx1_commitment,
        };
        let nested_s_prime_rx =
            nested::stages::s_prime::Stage::<C::HostCurve, R>::rx(&nested_s_prime_witness)?;
        let nested_s_prime_blind = C::ScalarField::random(&mut *rng);
        let nested_s_prime_commitment =
            nested_s_prime_rx.commit(C::nested_generators(self.params), nested_s_prime_blind);

        Ok(proof::SPrime {
            mesh_wx0_poly: native_mesh_wx0_poly,
            mesh_wx0_blind: native_mesh_wx0_blind,
            mesh_wx0_commitment: native_mesh_wx0_commitment,
            mesh_wx1_poly: native_mesh_wx1_poly,
            mesh_wx1_blind: native_mesh_wx1_blind,
            mesh_wx1_commitment: native_mesh_wx1_commitment,
            nested_s_prime_rx,
            nested_s_prime_blind,
            nested_s_prime_commitment,
        })
    }
}
