//! Compressed proof structures and operations.

use alloc::vec::Vec;

use ff::{Field, PrimeField};
use ragu_arithmetic::Cycle;
use ragu_circuits::polynomials::Rank;
use ragu_core::{
    Result,
    drivers::emulator::{Emulator, Wireless},
    maybe::Always,
};
use ragu_primitives::{Element, GadgetExt};
use rand::CryptoRng;

use super::{Blind, IPA_TAG, IpaProof, absorb_point, prover, verifier};
use crate::{internal::transcript::Transcript, proof::Proof};

/// Succinct proof for external verification.
///
/// Currently only covers the $P(u) = v$ opening. The revdot-to-polynomial
/// reduction that binds $a$, $b$ to the claimed inner product is intentionally
/// out of scope at this layer and will be added on top of this IPA foundation.
#[derive(Clone, Debug)]
pub struct CompressedProof<C: Cycle> {
    /// P polynomial commitment.
    pub p_commitment: C::HostCurve,
    /// Evaluation point.
    pub u: C::CircuitField,
    /// Claimed evaluation $P(u)$.
    pub v: C::CircuitField,
    /// IPA opening proof for $P(u) = v$.
    pub ipa: IpaProof<C::HostCurve>,
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> crate::Application<'_, C, R, HEADER_SIZE> {
    /// Compress an uncompressed proof into succinct form.
    pub fn compress<RNG: CryptoRng>(
        &self,
        proof: &Proof<C, R>,
        rng: &mut RNG,
    ) -> Result<CompressedProof<C>>
    where
        C::CircuitField: PrimeField,
        C::ScalarField: PrimeField,
    {
        let generators = C::host_generators(self.params);
        let mut dr = Emulator::<Wireless<Always<()>, C::CircuitField>>::execute();
        let mut transcript = Transcript::new(&mut dr, C::circuit_poseidon(self.params), IPA_TAG)?;

        let p_commitment = proof.native_p_commitment();
        let u = proof.u;
        let v = proof.v();

        absorb_point::<C>(&mut dr, &mut transcript, &p_commitment)?;
        Element::constant(&mut dr, u).write(&mut dr, &mut transcript)?;
        Element::constant(&mut dr, v).write(&mut dr, &mut transcript)?;

        // Ragu's native polynomial commitments are non-hiding (rerandomization
        // provides ZK); pass zero as the blinding factor so the IPA's
        // reconstructed commitment matches `native_p_commitment` exactly.
        let p_coeffs: Vec<_> = proof.native_p_poly().iter_coeffs().collect();
        let ipa = prover::create_proof::<C, _, _>(
            generators,
            rng,
            &mut dr,
            &mut transcript,
            &p_coeffs,
            Blind(C::CircuitField::ZERO),
            u,
        )?;

        Ok(CompressedProof {
            p_commitment,
            u,
            v,
            ipa,
        })
    }

    /// Verify a compressed proof.
    pub fn verify_compressed(&self, compressed: &CompressedProof<C>) -> Result<bool>
    where
        C::CircuitField: PrimeField,
        C::ScalarField: PrimeField,
    {
        let generators = C::host_generators(self.params);
        let mut dr = Emulator::<Wireless<Always<()>, C::CircuitField>>::execute();
        let mut transcript = Transcript::new(&mut dr, C::circuit_poseidon(self.params), IPA_TAG)?;

        absorb_point::<C>(&mut dr, &mut transcript, &compressed.p_commitment)?;
        Element::constant(&mut dr, compressed.u).write(&mut dr, &mut transcript)?;
        Element::constant(&mut dr, compressed.v).write(&mut dr, &mut transcript)?;

        verifier::verify_proof::<C, _>(
            generators,
            &mut dr,
            &mut transcript,
            compressed.p_commitment,
            compressed.u,
            compressed.v,
            &compressed.ipa,
        )
    }
}

#[cfg(test)]
mod tests {
    use ragu_circuits::polynomials::R;
    use ragu_pasta::Pasta;
    use rand::{SeedableRng, rngs::StdRng};

    use crate::ApplicationBuilder;

    type TestR = R<13>;
    const HEADER_SIZE: usize = 4;

    fn create_test_app() -> crate::Application<'static, Pasta, TestR, HEADER_SIZE> {
        let pasta = Pasta::baked();
        ApplicationBuilder::<Pasta, TestR, HEADER_SIZE>::new()
            .finalize(pasta)
            .expect("failed to create test application")
    }

    #[test]
    fn test_compress_and_verify() {
        let app = create_test_app();
        let mut rng = StdRng::seed_from_u64(54321);

        let proof = app.trivial_proof();
        let compressed = app.compress(&proof, &mut rng).unwrap();
        assert!(app.verify_compressed(&compressed).unwrap());
    }
}
