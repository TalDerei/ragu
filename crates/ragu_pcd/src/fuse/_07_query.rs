//! Commit to the polynomial query claims at various points ($x$, $xz$, $w$, and
//! $\omega^i$ for various internal circuits).
//!
//! This sets the native `query` stage containing the claimed evaluations at
//! various points that are then relied on in the revdot claims infrastructure.
//! (See the `compute_v` circuit.)
//!
//! This phase of the fuse operation is also used to commit to the $m(W, x, y)$
//! restriction.

use ff::Field;
use ragu_arithmetic::{Cycle, bitreverse, par_join};
use ragu_circuits::{polynomials::Rank, staging::StageExt};
use ragu_core::{Result, drivers::Driver, maybe::Maybe};
use ragu_primitives::Element;
use rand::CryptoRng;

use super::RegistryWy;
use crate::{Application, Proof, internal::native, proof::ProofBuilder};

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    pub(super) fn compute_query<'dr, D, RNG: CryptoRng>(
        &self,
        rng: &mut RNG,
        w: &Element<'dr, D>,
        x: &Element<'dr, D>,
        y: &Element<'dr, D>,
        z: &Element<'dr, D>,
        registry_wy: &RegistryWy<C, R>,
        left: &Proof<C, R>,
        right: &Proof<C, R>,
        builder: &mut ProofBuilder<'_, C, R>,
    ) -> Result<native::stages::query::Witness<C>>
    where
        D: Driver<'dr, F = C::CircuitField>,
    {
        let w = *w.value().take();
        let x = *x.value().take();
        let y = *y.value().take();
        let xz = x * *z.value().take();

        let registry_xy_evals = self.native_registry.wxy_over_domain(x, y);
        let log2_n = self.native_registry.log2_domain();

        let fixed_registry = native::InternalCircuitValues::from_fn(|id| {
            let i = usize::from(id.circuit_index()) as u32;
            registry_xy_evals[bitreverse(i, log2_n) as usize]
        });
        let registry_xy_poly = self.native_registry.interpolate_xy(registry_xy_evals);

        // Evaluate the registry polynomial at w concurrently with the
        // left/right child witness construction.
        let (registry_wxy, left_witness, right_witness) = par_join!(
            || registry_xy_poly.eval(w),
            || native::stages::query::ChildEvaluationsWitness::from_proof(
                left,
                w,
                x,
                xz,
                &registry_xy_poly,
                &registry_wy.poly,
            ),
            || native::stages::query::ChildEvaluationsWitness::from_proof(
                right,
                w,
                x,
                xz,
                &registry_xy_poly,
                &registry_wy.poly,
            ),
        );

        let query_witness = native::stages::query::Witness {
            fixed_registry,
            registry_wxy,
            left: left_witness,
            right: right_witness,
        };

        let rx = native::stages::query::Stage::<C, R, HEADER_SIZE>::rx(
            C::CircuitField::random(&mut *rng),
            &query_witness,
        )?;

        builder.set_native_query_rx(rx);
        builder.set_native_registry_xy_poly(registry_xy_poly);

        Ok(query_witness)
    }
}
