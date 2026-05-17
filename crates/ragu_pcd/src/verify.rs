//! This module provides the [`Application::verify`] method implementation.

use core::iter::once;

use ff::Field;
use ragu_arithmetic::Cycle;
use ragu_circuits::{
    polynomials::{Rank, sparse},
    registry::CircuitIndex,
    staging::{Stage, StageExt, verify_stage_support},
};
use ragu_core::{Result, drivers::emulator::Emulator, maybe::Maybe};
use ragu_primitives::Element;
use rand::CryptoRng;

use crate::{
    Application, Pcd, Proof,
    header::Header,
    internal::{
        claims,
        native::{
            RevdotParameters, RxIndex, claims as native_claims, stages,
            stages::preamble::ProofInputs,
        },
        nested::claims as nested_claims,
    },
};

/// Per-rx structural well-formedness check for every native stage in the proof.
///
/// Each stage rx is pinned to its own gate window: nonzero coefficients must
/// live on the `(a, d)` wires at gate `0` (SYSTEM) or within
/// `[skip, skip + num)` for that stage. Rxs that place coefficients outside
/// their stage's own window are rejected.
///
/// Returns `true` if every native stage rx is admissible.
fn verify_native_stage_supports<C: Cycle, R: Rank, const HEADER_SIZE: usize>(
    proof: &Proof<C, R>,
) -> bool {
    let stage_windows: [(RxIndex, usize, usize); 5] = [
        (
            RxIndex::Preamble,
            <stages::preamble::Stage<C, R, HEADER_SIZE>>::skip_gates(),
            <stages::preamble::Stage<C, R, HEADER_SIZE> as StageExt<_, _>>::num_gates(),
        ),
        (
            RxIndex::OuterError,
            <stages::outer_error::Stage<C, R, HEADER_SIZE, RevdotParameters>>::skip_gates(),
            <stages::outer_error::Stage<C, R, HEADER_SIZE, RevdotParameters> as StageExt<
                _,
                _,
            >>::num_gates(),
        ),
        (
            RxIndex::InnerError,
            <stages::inner_error::Stage<C, R, HEADER_SIZE, RevdotParameters>>::skip_gates(),
            <stages::inner_error::Stage<C, R, HEADER_SIZE, RevdotParameters> as StageExt<
                _,
                _,
            >>::num_gates(),
        ),
        (
            RxIndex::Query,
            <stages::query::Stage<C, R, HEADER_SIZE>>::skip_gates(),
            <stages::query::Stage<C, R, HEADER_SIZE> as StageExt<_, _>>::num_gates(),
        ),
        (
            RxIndex::Eval,
            <stages::eval::Stage<C, R, HEADER_SIZE>>::skip_gates(),
            <stages::eval::Stage<C, R, HEADER_SIZE> as StageExt<_, _>>::num_gates(),
        ),
    ];

    stage_windows
        .into_iter()
        .all(|(idx, skip, num)| verify_stage_support(&proof[idx], skip, num))
}

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    /// Verifies some [`Pcd`] for the provided [`Header`].
    ///
    /// Returns `Ok(true)` if all verification checks pass, `Ok(false)` if
    /// any check fails (e.g., invalid circuit ID, header size mismatch,
    /// corrupted commitments or evaluations), or `Err` if an internal
    /// computation error occurs.
    pub fn verify<RNG: CryptoRng, H: Header<C::CircuitField>>(
        &self,
        pcd: &Pcd<C, R, H>,
        mut rng: RNG,
    ) -> Result<bool> {
        // Sample verification challenges w, y, and z.
        let w = C::CircuitField::random(&mut rng);
        let y = C::CircuitField::random(&mut rng);
        let z = C::CircuitField::random(&mut rng);

        // Validate that the application circuit_id is within the registry domain.
        // (Internal circuit IDs are constants and don't need this check.)
        if !self
            .native_registry
            .circuit_in_domain(pcd.proof().circuit_id())
        {
            return Ok(false);
        }

        // Validate that the `left_header` and `right_header` lengths match
        // `HEADER_SIZE`. Alternatively, the `Proof` structure could be
        // parameterized on the `HEADER_SIZE`, but this appeared to be simpler.
        if pcd.proof().left_header().len() != HEADER_SIZE
            || pcd.proof().right_header().len() != HEADER_SIZE
        {
            return Ok(false);
        }

        // Validate per-stage rx well-formedness. The bundled bonding identity
        // only catches plants outside the union of all bundled stages' windows;
        // this structural check rejects plants inside another bundled stage's
        // window that the bundled revdot would miss.
        if !verify_native_stage_supports::<C, R, HEADER_SIZE>(pcd.proof()) {
            return Ok(false);
        }

        // Compute unified k(y), unified_bridge k(y), and application k(y).
        let (unified_ky, unified_bridge_ky, application_ky) =
            Emulator::emulate_wireless((pcd.proof(), pcd.data().clone(), y), |dr, witness| {
                let (proof, data, y) = witness.cast();
                let y = Element::alloc(dr, &mut (), y)?;
                let proof_inputs =
                    ProofInputs::<_, C, HEADER_SIZE>::alloc_for_verify::<R, H>(dr, proof, data)?;

                let (unified_ky, unified_bridge_ky) = proof_inputs.unified_ky_values(dr, &y)?;
                let unified_ky = *unified_ky.value().take();
                let unified_bridge_ky = *unified_bridge_ky.value().take();
                let application_ky = *proof_inputs.application_ky(dr, &y)?.value().take();

                Ok((unified_ky, unified_bridge_ky, application_ky))
            })?;

        // Build a and b polynomials for each revdot claim.
        let source = native::SingleProofSource { proof: pcd.proof() };
        let mut builder = claims::Builder::new(&self.native_registry, y, z);
        native_claims::build(&source, &mut builder)?;

        // Check all native revdot claims.
        let native_revdot_claims = {
            let ky_source = native::SingleProofKySource {
                // NOTE: `raw_c` is now computed as `revdot(a, b)` rather
                // than stored in the proof, so this claim is tautological
                // in the verifier. It remains meaningful inside the circuit
                // where `c` is an independently allocated witness element.
                raw_c: pcd.proof().c(),
                application_ky,
                unified_bridge_ky,
                unified_ky,
            };

            native::ky_values(&ky_source)
                .zip(builder.a.iter().zip(builder.b.iter()))
                .all(|(ky, (a, b))| a.revdot(b) == ky)
        };

        // Check all nested revdot claims.
        let nested_revdot_claims = {
            let nested_source = nested::SingleProofSource { proof: pcd.proof() };
            let y_nested = C::ScalarField::random(&mut rng);
            let z_nested = C::ScalarField::random(&mut rng);
            let mut nested_builder =
                claims::Builder::new(&self.nested_registry, y_nested, z_nested);
            nested_claims::build(&nested_source, &mut nested_builder)?;

            let ky_source = nested::SingleProofKySource::<C::ScalarField>::new();
            nested::ky_values(&ky_source)
                .zip(nested_builder.a.iter().zip(nested_builder.b.iter()))
                .all(|(ky, (a, b))| a.revdot(b) == ky)
        };

        // Check registry_xy polynomial evaluation at the sampled w.
        // registry_xy_poly is m(W, x, y) - the registry evaluated at current x, y, free in W.
        let registry_xy_claim = {
            let x = pcd.proof().x();
            let y = pcd.proof().y();
            let poly_eval = pcd.proof().native_registry_xy_poly().eval(w);
            let expected = self.native_registry.wxy(w, x, y);
            poly_eval == expected
        };

        // TODO: Add checks for registry_wx0_poly, registry_wx1_poly, and registry_wy_poly.
        // - registry_wx0/wx1: need child proof x challenges (x₀, x₁) which "disappear" in preamble
        // - registry_wy: interstitial value that will be elided later

        Ok(native_revdot_claims && nested_revdot_claims && registry_xy_claim)
    }
}

mod native {
    use super::*;
    pub use crate::internal::native::claims::ky_values;
    use crate::internal::{
        claims::Source,
        native::{RxComponent, claims::KySource},
    };

    pub struct SingleProofSource<'rx, C: Cycle, R: Rank> {
        pub proof: &'rx Proof<C, R>,
    }

    impl<'rx, C: Cycle, R: Rank> Source for SingleProofSource<'rx, C, R> {
        type RxComponent = RxComponent;
        type Rx = &'rx sparse::Polynomial<C::CircuitField, R>;
        type AppCircuitId = CircuitIndex;

        fn rx(&self, component: RxComponent) -> impl Iterator<Item = Self::Rx> {
            core::iter::once(&self.proof[component])
        }

        fn app_circuits(&self) -> impl Iterator<Item = Self::AppCircuitId> {
            core::iter::once(self.proof.circuit_id())
        }
    }

    /// Source for k(y) values for single-proof verification.
    pub struct SingleProofKySource<F> {
        pub raw_c: F,
        pub application_ky: F,
        pub unified_bridge_ky: F,
        pub unified_ky: F,
    }

    impl<F: Field> KySource for SingleProofKySource<F> {
        type Ky = F;

        fn raw_c(&self) -> impl Iterator<Item = F> {
            once(self.raw_c)
        }

        fn application_ky(&self) -> impl Iterator<Item = F> {
            once(self.application_ky)
        }

        fn unified_bridge_ky(&self) -> impl Iterator<Item = F> {
            once(self.unified_bridge_ky)
        }

        fn unified_ky(&self) -> impl Iterator<Item = F> + Clone {
            once(self.unified_ky)
        }

        fn zero(&self) -> F {
            F::ZERO
        }
    }
}

mod nested {
    use super::*;
    pub use crate::internal::nested::claims::ky_values;
    use crate::internal::{
        claims::Source,
        nested::{RxIndex, claims::KySource},
    };

    /// Source for nested field rx polynomials for single-proof verification.
    pub struct SingleProofSource<'rx, C: Cycle, R: Rank> {
        pub proof: &'rx Proof<C, R>,
    }

    impl<'rx, C: Cycle, R: Rank> Source for SingleProofSource<'rx, C, R> {
        type RxComponent = RxIndex;
        type Rx = &'rx sparse::Polynomial<C::ScalarField, R>;
        type AppCircuitId = ();

        fn rx(&self, component: RxIndex) -> impl Iterator<Item = Self::Rx> {
            core::iter::once(&self.proof[component])
        }

        fn app_circuits(&self) -> impl Iterator<Item = Self::AppCircuitId> {
            core::iter::empty()
        }
    }

    /// Source for k(y) values for nested single-proof verification.
    pub struct SingleProofKySource<F>(core::marker::PhantomData<F>);

    impl<F> SingleProofKySource<F> {
        pub fn new() -> Self {
            Self(core::marker::PhantomData)
        }
    }

    impl<F: Field> KySource for SingleProofKySource<F> {
        type Ky = F;

        fn one(&self) -> F {
            F::ONE
        }

        fn zero(&self) -> F {
            F::ZERO
        }
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use ragu_circuits::{polynomials::ProductionRank, registry::CircuitIndex};
    use ragu_pasta::Pasta;
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::ApplicationBuilder;

    type TestR = ProductionRank;
    const HEADER_SIZE: usize = 4;

    fn create_test_app() -> crate::Application<'static, Pasta, TestR, HEADER_SIZE> {
        let pasta = Pasta::baked();
        ApplicationBuilder::<Pasta, TestR, HEADER_SIZE>::new()
            .finalize(pasta)
            .expect("failed to create test application")
    }

    #[test]
    fn verify_rejects_invalid_circuit_id() {
        let app = create_test_app();
        let mut rng = StdRng::seed_from_u64(1234);

        // Create a valid trivial proof
        let mut proof = app.trivial_proof();

        // Corrupt the circuit_id to be outside the registry domain
        proof.circuit_id = CircuitIndex::new(u32::MAX as usize);

        let pcd = proof.carry::<()>(());
        let result = app.verify(&pcd, &mut rng).expect("verify should not error");
        assert!(!result, "verify should reject invalid circuit_id");
    }

    #[test]
    fn verify_rejects_wrong_left_header_size() {
        let app = create_test_app();
        let mut rng = StdRng::seed_from_u64(1234);

        // Create a valid trivial proof
        let mut proof = app.trivial_proof();

        // Corrupt left_header to have wrong size
        proof.left_header = alloc::vec![<Pasta as Cycle>::CircuitField::ZERO; HEADER_SIZE + 1];

        let pcd = proof.carry::<()>(());
        let result = app.verify(&pcd, &mut rng).expect("verify should not error");
        assert!(!result, "verify should reject wrong left_header size");
    }

    #[test]
    fn verify_rejects_wrong_right_header_size() {
        let app = create_test_app();
        let mut rng = StdRng::seed_from_u64(1234);

        // Create a valid trivial proof
        let mut proof = app.trivial_proof();

        // Corrupt right_header to have wrong size
        proof.right_header = alloc::vec![<Pasta as Cycle>::CircuitField::ZERO; HEADER_SIZE - 1];

        let pcd = proof.carry::<()>(());
        let result = app.verify(&pcd, &mut rng).expect("verify should not error");
        assert!(!result, "verify should reject wrong right_header size");
    }

    /// End-to-end check that the per-stage support fence catches a
    /// malformed stage rx that the bundled bonding revdot would miss.
    ///
    /// Plant a nonzero coefficient on `native_outer_error_rx`'s a-wire at
    /// gate 500. Stage `OuterError`'s own window is `[226, 360)`; stage
    /// `InnerError`'s window is `[360, 696)`. Gate 500 lies inside
    /// `InnerError`'s window — i.e. inside the bundled `OuterInnerError`
    /// union — so the bundled mask is zero there and the bundled revdot
    /// would not detect the planted entry. The support fence rejects it
    /// because gate 500 lies outside `OuterError`'s own window.
    #[test]
    fn verify_rejects_native_stage_rx_planted_outside_its_window() {
        use ragu_pasta::Fp;

        use crate::step::internal::trivial::Trivial;

        let app = create_test_app();
        let mut rng = StdRng::seed_from_u64(1234);

        // Baseline: an honestly-seeded leaf (trivial step) verifies.
        let (leaf, _) = app.seed(&mut rng, Trivial::new(), ()).unwrap();
        assert!(
            app.verify(&leaf, &mut StdRng::seed_from_u64(5678)).unwrap(),
            "honestly-seeded trivial leaf must verify",
        );

        // Plant a `0xDEADBEEF` on `native_outer_error_rx`'s a-wire at gate 500.
        // Gate 500 is inside InnerError's window [360, 696) (the OuterInnerError
        // bundle's union) and outside OuterError's own window [226, 360).
        let mut tampered = leaf;
        let n = <TestR as Rank>::n();
        const PLANTED_GATE: usize = 500;
        let mut coeffs = alloc::vec![Fp::ZERO; <TestR as Rank>::num_coeffs()];
        coeffs[2 * n - 1 - PLANTED_GATE] = Fp::from(0xDEADBEEFu64);
        tampered.proof_mut().native_outer_error_rx =
            sparse::Polynomial::<Fp, TestR>::from_coeffs(coeffs);

        let result = app
            .verify(&tampered, &mut StdRng::seed_from_u64(5678))
            .expect("verify should not error");
        assert!(
            !result,
            "tampered leaf must be rejected by the per-stage support fence",
        );
    }
}
