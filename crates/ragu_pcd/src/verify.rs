//! This module provides the [`Application::verify`] method implementation.

use core::iter::once;

use ragu_arithmetic::{CryptoRngCore, Cycle, ff::Field};
use ragu_circuits::{
    polynomials::{Rank, sparse},
    registry::CircuitIndex,
};
use ragu_core::{Result, drivers::emulator::Emulator, maybe::Maybe};
use ragu_primitives::Element;

use crate::{
    Application, Pcd, Proof,
    header::Header,
    internal::{
        claims,
        native::{claims as native_claims, stages::preamble::ProofInputs},
        nested::claims as nested_claims,
    },
};

impl<C: Cycle, R: Rank, const HEADER_SIZE: usize> Application<'_, C, R, HEADER_SIZE> {
    /// Verifies some [`Pcd`] for the provided [`Header`].
    ///
    /// Returns `Ok(true)` if all verification checks pass, `Ok(false)` if
    /// any check fails (e.g., invalid circuit ID, header size mismatch,
    /// corrupted commitments or evaluations), or `Err` if an internal
    /// computation error occurs.
    pub fn verify<RNG: CryptoRngCore, H: Header<C::CircuitField>>(
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
    use ragu_arithmetic::{
        ff::Field,
        rand::{SeedableRng, rngs::StdRng},
    };
    use ragu_circuits::{
        polynomials::{ProductionRank, sparse},
        registry::CircuitIndex,
    };
    use ragu_core::drivers::{Driver, DriverValue};
    use ragu_pasta::Pasta;
    use ragu_primitives::allocator::Standard;

    use super::*;
    use crate::{
        ApplicationBuilder,
        step::{Encoded, Index, Step},
    };

    type TestR = ProductionRank;
    const HEADER_SIZE: usize = 4;

    fn create_test_app() -> crate::Application<'static, Pasta, TestR, HEADER_SIZE> {
        let pasta = Pasta::baked();
        ApplicationBuilder::<Pasta, TestR, HEADER_SIZE>::new()
            .finalize(pasta)
            .expect("failed to create test application")
    }

    struct UnitStep<const I: usize>;

    impl<const I: usize> Step<Pasta> for UnitStep<I> {
        const INDEX: Index = Index::new(I);

        type Witness<'source> = ();
        type Aux<'source> = ();
        type Left = ();
        type Right = ();
        type Output = ();

        fn witness<
            'dr,
            'source: 'dr,
            D: Driver<'dr, F = <Pasta as Cycle>::CircuitField>,
            const HS: usize,
        >(
            &self,
            dr: &mut D,
            _: DriverValue<D, Self::Witness<'source>>,
            left: DriverValue<D, ()>,
            right: DriverValue<D, ()>,
        ) -> Result<(
            (
                Encoded<'dr, D, Self::Left, HS>,
                Encoded<'dr, D, Self::Right, HS>,
                Encoded<'dr, D, Self::Output, HS>,
            ),
            DriverValue<D, ()>,
            DriverValue<D, ()>,
        )>
        where
            Self: 'dr,
        {
            let allocator = &mut Standard::new();
            Ok((
                (
                    Encoded::new(dr, allocator, left)?,
                    Encoded::new(dr, allocator, right)?,
                    Encoded::from_gadget(()),
                ),
                D::unit(),
                D::unit(),
            ))
        }
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

    #[test]
    fn base_case_confined_to_bootstrap_rejects_invalid_unit_children() {
        // Regression test for the base-case over-broadness closed by confining
        // the base case to the internal `Trivial` step (see `is_base_case`).
        //
        // Previously any fuse whose step declared `()` inputs was treated as a
        // base case, so the child revdot claim was skipped and a corrupted
        // `Pcd<()>` slipped through. Now only a step declaring `Bootstrap`
        // inputs triggers it, so an application step's children always have
        // their claims enforced and the forgery is rejected.
        let pasta = Pasta::baked();
        let app = ApplicationBuilder::<Pasta, TestR, HEADER_SIZE>::new()
            .register(UnitStep::<0>)
            .expect("register seed step")
            .register(UnitStep::<1>)
            .expect("register fuse step")
            .finalize(pasta)
            .expect("failed to create test application");

        // Genuine seed still works: it now fuses against the bootstrapped
        // seeded-trivial proof, so an honestly produced unit proof verifies.
        let mut rng = StdRng::seed_from_u64(1);
        let (valid_unit, ()) = app.seed(&mut rng, UnitStep::<0>, ()).expect("seed");
        assert!(
            app.verify(&valid_unit, StdRng::seed_from_u64(2))
                .expect("valid child verify should not error"),
            "honestly produced unit proof should still verify"
        );

        // Corrupt the produced unit proof so it no longer verifies on its own.
        let (mut invalid_child, ()) = valid_unit.into_parts();
        invalid_child
            .native_a_poly
            .add_assign(&sparse::Polynomial::from_coeffs(alloc::vec![
                <Pasta as Cycle>::CircuitField::ONE,
            ]));
        let invalid_child = invalid_child.carry::<()>(());

        assert!(
            !app.verify(&invalid_child, StdRng::seed_from_u64(3))
                .expect("invalid child verify should not error"),
            "corrupted child proof should not verify on its own"
        );

        // Fusing the corrupted children through a unit step no longer receives
        // base-case treatment: `UnitStep` declares `()` inputs, not `Bootstrap`,
        // so the revdot claim is enforced. The forgery must be rejected — either
        // the fuse fails to assemble a satisfying trace, or the resulting parent
        // fails to verify.
        match app.fuse(
            &mut rng,
            UnitStep::<1>,
            (),
            invalid_child.clone(),
            invalid_child,
        ) {
            Err(_) => {
                // Prover could not satisfy the now-enforced revdot claim.
            }
            Ok((parent, ())) => {
                assert!(
                    !app.verify(&parent, StdRng::seed_from_u64(4))
                        .expect("parent verify should not error"),
                    "a parent fused from invalid children must not verify"
                );
            }
        }
    }

    #[test]
    fn registration_rejects_an_application_header_claiming_a_reserved_suffix() {
        // The base case fires when the current step declares the `Bootstrap`
        // suffix for both inputs, so an application header must never be able to
        // encode to a reserved suffix. `Bootstrap` itself is crate-private, but
        // the encoded suffix is just a number, so registration guards the number
        // rather than the type.
        use crate::header::{Header, Suffix};

        struct ReservedHeader;

        impl Header<<Pasta as Cycle>::CircuitField> for ReservedHeader {
            // Reach the reserved value directly; `Suffix::new` separately
            // prevents reaching it by overflowing the application offset.
            const SUFFIX: Suffix = Suffix::bootstrap();
            type Data = ();
            type Output = ();

            fn encode<
                'dr,
                D: Driver<'dr, F = <Pasta as Cycle>::CircuitField>,
                A: ragu_primitives::allocator::Allocator<'dr, D>,
            >(
                _: &mut D,
                _: &mut A,
                _: DriverValue<D, Self::Data>,
            ) -> Result<ragu_core::gadgets::Bound<'dr, D, Self::Output>> {
                Ok(())
            }
        }

        struct ReservedStep;

        impl Step<Pasta> for ReservedStep {
            const INDEX: Index = Index::new(0);

            type Witness<'source> = ();
            type Aux<'source> = ();
            type Left = ReservedHeader;
            type Right = ReservedHeader;
            type Output = ();

            fn witness<
                'dr,
                'source: 'dr,
                D: Driver<'dr, F = <Pasta as Cycle>::CircuitField>,
                const HS: usize,
            >(
                &self,
                dr: &mut D,
                _: DriverValue<D, Self::Witness<'source>>,
                left: DriverValue<D, ()>,
                right: DriverValue<D, ()>,
            ) -> Result<(
                (
                    Encoded<'dr, D, Self::Left, HS>,
                    Encoded<'dr, D, Self::Right, HS>,
                    Encoded<'dr, D, Self::Output, HS>,
                ),
                DriverValue<D, ()>,
                DriverValue<D, ()>,
            )>
            where
                Self: 'dr,
            {
                let allocator = &mut Standard::new();
                Ok((
                    (
                        Encoded::new(dr, allocator, left)?,
                        Encoded::new(dr, allocator, right)?,
                        Encoded::from_gadget(()),
                    ),
                    D::unit(),
                    D::unit(),
                ))
            }
        }

        assert!(
            ApplicationBuilder::<Pasta, TestR, HEADER_SIZE>::new()
                .register(ReservedStep)
                .is_err(),
            "registering an application header on a reserved suffix must fail"
        );
    }

    #[test]
    fn forged_child_headers_cannot_trigger_the_base_case() {
        // Base-case detection reads the suffix of the header the *current* step
        // declared for each child, which `padded::for_header` emits as a circuit
        // constant. It is not read from the child proof, so writing the reserved
        // `Bootstrap` suffix into a child's stored headers — which a prover fully
        // controls, and which `verify` only length-checks — must not buy
        // base-case treatment.
        let pasta = Pasta::baked();
        let app = ApplicationBuilder::<Pasta, TestR, HEADER_SIZE>::new()
            .register(UnitStep::<0>)
            .expect("register seed step")
            .register(UnitStep::<1>)
            .expect("register fuse step")
            .finalize(pasta)
            .expect("failed to create test application");

        let mut rng = StdRng::seed_from_u64(11);
        let (valid_unit, ()) = app.seed(&mut rng, UnitStep::<0>, ()).expect("seed");

        let (mut invalid_child, ()) = valid_unit.into_parts();
        invalid_child
            .native_a_poly
            .add_assign(&sparse::Polynomial::from_coeffs(alloc::vec![
                <Pasta as Cycle>::CircuitField::ONE,
            ]));

        // Stamp the reserved bootstrap suffix into the child's stored headers.
        let mut forged = alloc::vec![<Pasta as Cycle>::CircuitField::ZERO; HEADER_SIZE];
        forged[HEADER_SIZE - 1] =
            <Pasta as Cycle>::CircuitField::from(crate::header::Suffix::bootstrap().get());
        invalid_child.left_header = forged.clone();
        invalid_child.right_header = forged;

        let invalid_child = invalid_child.carry::<()>(());

        match app.fuse(
            &mut rng,
            UnitStep::<1>,
            (),
            invalid_child.clone(),
            invalid_child,
        ) {
            Err(_) => {
                // Prover could not satisfy the still-enforced revdot claim.
            }
            Ok((parent, ())) => {
                assert!(
                    !app.verify(&parent, StdRng::seed_from_u64(12))
                        .expect("parent verify should not error"),
                    "forged bootstrap suffixes in child headers must not trigger the base case"
                );
            }
        }
    }

    #[test]
    fn rerandomize_unit_proof_still_verifies() {
        // A `Pcd<()>` used to trip the over-broad base case during
        // rerandomization (both fuse inputs carried a `()` output), silently
        // dropping its revdot claim. With the base case confined to `Trivial`,
        // `Rerandomize` never triggers it, so rerandomize takes the normal
        // claim-enforcing path — and must still preserve verification.
        let pasta = Pasta::baked();
        let app = ApplicationBuilder::<Pasta, TestR, HEADER_SIZE>::new()
            .register(UnitStep::<0>)
            .expect("register seed step")
            .finalize(pasta)
            .expect("failed to create test application");

        let mut rng = StdRng::seed_from_u64(7);
        let (unit, ()) = app.seed(&mut rng, UnitStep::<0>, ()).expect("seed");
        assert!(
            app.verify(&unit, StdRng::seed_from_u64(8))
                .expect("verify should not error"),
            "seeded unit proof should verify"
        );

        let rerandomized = app.rerandomize(unit, &mut rng).expect("rerandomize");
        assert!(
            app.verify(&rerandomized, StdRng::seed_from_u64(9))
                .expect("verify should not error"),
            "rerandomized unit proof should still verify through the enforced path"
        );
    }
}
