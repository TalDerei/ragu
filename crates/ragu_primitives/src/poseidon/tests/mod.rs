//! Tests for the Poseidon sponge and permutation.

mod halo2_vectors;

use core::cell::Cell;

use ragu_arithmetic::Cycle;
use ragu_core::maybe::Maybe;
use ragu_pasta::{Fp, Pasta};

use self::halo2_vectors::{FP_PERMUTE_VECTORS, FQ_PERMUTE_VECTORS, P128Pow5T3Fp, P128Pow5T3Fq};
use super::*;

type Simulator = crate::Simulator<Fp>;
use crate::allocator::Standard;

/// Run [`Permutation`] over each `(initial_state, final_state)` vector and
/// compare the full permuted state.
///
/// The vectors are external -- halo2's, transcribed from
/// zcash-test-vectors -- so this pins the permutation to a reference
/// outside this repository. It pins the *construction*, not the parameters
/// ragu ships: the round ordering, the sbox placement, the full/partial
/// split, the MDS application, and the point at which round constants are
/// added are all generic over
/// [`PoseidonPermutation`](ragu_arithmetic::PoseidonPermutation), so
/// running them at Orchard's t=3 instantiation exercises the same code the
/// t=5 one ragu deploys goes through. What it does not reach is behaviour
/// specific to a width -- the state and MDS loops at t=5 -- which is what
/// `fuzz_poseidon_sponge` and `fuzz_poseidon_differential` cover. The
/// parameters themselves are checked separately, against the generator that
/// produced them, by `qa/params`.
fn check_permutation_vectors<F, P>(params: &'static P, vectors: &[([F; 3], [F; 3])]) -> Result<()>
where
    F: Field,
    P: ragu_arithmetic::PoseidonPermutation<F>,
{
    assert_eq!(P::T, 3, "the vendored vectors are for a width-3 state");
    assert!(!vectors.is_empty(), "no test vectors");

    for (index, (initial, expected)) in vectors.iter().enumerate() {
        let mut actual = [F::ZERO; 3];

        crate::Simulator::<F>::simulate(*initial, |dr, witness| {
            let allocator = &mut Standard::new();
            let values = (0..P::T)
                .map(|i| Element::alloc(dr, allocator, witness.as_ref().map(|v| v[i])))
                .collect::<Result<Vec<_>>>()?;

            let state = SpongeState::<'_, _, P>::from_elements(
                values.try_into().expect("P::T is the state length"),
            );
            let permuted = dr.routine(Permutation::from(params), state)?;

            for (slot, element) in actual.iter_mut().zip(permuted.into_elements().iter()) {
                *slot = *element.value().take();
            }

            Ok(())
        })?;

        assert_eq!(
            actual, *expected,
            "permutation output differs from halo2 test vector {index}"
        );
    }

    Ok(())
}

#[test]
fn permutation_matches_halo2_vectors_fp() -> Result<()> {
    check_permutation_vectors(&P128Pow5T3Fp, FP_PERMUTE_VECTORS)
}

#[test]
fn permutation_matches_halo2_vectors_fq() -> Result<()> {
    check_permutation_vectors(&P128Pow5T3Fq, FQ_PERMUTE_VECTORS)
}

#[test]
fn test_permutation_constraints() -> Result<()> {
    let params = Pasta::baked();

    let sim = Simulator::simulate(Fp::from(1), |dr, value| {
        let mut sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
            dr,
            Pasta::circuit_poseidon(params),
        );
        let allocator = &mut Standard::new();
        let value = Element::alloc(dr, allocator, value)?;
        sponge.absorb(dr, &value)?;

        dr.reset();
        sponge.squeeze(dr)?;

        Ok(())
    })?;
    assert_eq!(sim.num_gates(), 288);

    Ok(())
}

#[test]
fn test_save_state_nothing_absorbed() -> Result<()> {
    let params = Pasta::baked();

    Simulator::simulate((), |dr, _| {
        let sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
            dr,
            Pasta::circuit_poseidon(params),
        );
        // Try to save without absorbing anything
        let result = sponge.save_state(dr);
        assert!(matches!(result, Err(SaveError::NothingAbsorbed)));

        Ok(())
    })?;

    Ok(())
}

#[test]
fn test_squeeze_before_any_absorb() -> Result<()> {
    let params = Pasta::baked();
    let mut dr = Simulator::new();
    let mut sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
        &mut dr,
        Pasta::circuit_poseidon(params),
    );

    // Squeeze without absorbing anything should fail
    assert!(sponge.squeeze(&mut dr).is_err());
    Ok(())
}

#[test]
fn test_save_state_already_in_squeeze_mode() -> Result<()> {
    let params = Pasta::baked();

    Simulator::simulate(Fp::from(1), |dr, value| {
        let mut sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
            dr,
            Pasta::circuit_poseidon(params),
        );
        let allocator = &mut Standard::new();
        let value = Element::alloc(dr, allocator, value)?;
        sponge.absorb(dr, &value)?;
        // Squeeze to enter squeeze mode
        sponge.squeeze(dr)?;
        // Now try to save - should fail
        let result = sponge.save_state(dr);
        assert!(matches!(result, Err(SaveError::AlreadyInSqueezeMode)));

        Ok(())
    })?;

    Ok(())
}

#[test]
fn test_save_state_succeeds_after_absorb() -> Result<()> {
    let params = Pasta::baked();

    Simulator::simulate(Fp::from(1), |dr, value| {
        let mut sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
            dr,
            Pasta::circuit_poseidon(params),
        );
        let allocator = &mut Standard::new();
        let value = Element::alloc(dr, allocator, value)?;
        sponge.absorb(dr, &value)?;
        // Save should succeed
        let _state = sponge.save_state(dr).expect("save_state should succeed");

        Ok(())
    })?;

    Ok(())
}

#[test]
fn test_save_resume_produces_same_output_as_normal_sponge() -> Result<()> {
    let params = Pasta::baked();

    // Use Cell to extract the output values from inside the closures
    let normal_output = Cell::new(Fp::ZERO);
    let save_resume_output = Cell::new(Fp::ZERO);

    // Run normal sponge flow and get squeezed value
    Simulator::simulate(Fp::from(123), |dr, value| {
        let mut sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
            dr,
            Pasta::circuit_poseidon(params),
        );
        let allocator = &mut Standard::new();
        let value = Element::alloc(dr, allocator, value)?;
        sponge.absorb(dr, &value)?;
        let squeezed = sponge.squeeze(dr)?;
        normal_output.set(*squeezed.value().take());
        Ok(())
    })?;

    // Run save/resume flow and get squeezed value
    Simulator::simulate(Fp::from(123), |dr, value| {
        let mut sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
            dr,
            Pasta::circuit_poseidon(params),
        );
        let allocator = &mut Standard::new();
        let value = Element::alloc(dr, allocator, value)?;
        sponge.absorb(dr, &value)?;
        let state = sponge.save_state(dr).expect("save_state should succeed");
        let mut sponge = Sponge::resume(state, Pasta::circuit_poseidon(params));
        let squeezed = sponge.squeeze(dr)?;
        save_resume_output.set(*squeezed.value().take());
        Ok(())
    })?;

    // Both should produce identical output
    assert_eq!(normal_output.get(), save_resume_output.get());

    Ok(())
}

#[test]
// Misuse: forgetting to squeeze after resuming put sponge in a bad state.
fn test_absorb_before_squeeze_after_resume() -> Result<()> {
    let params = Pasta::baked();

    let normal_output = Cell::new(Fp::ZERO);
    let bad_resume_output = Cell::new(Fp::ZERO);

    let witness = (Fp::from(1), Fp::from(2));

    // Normal flow: absorb v1, absorb v2, squeeze
    Simulator::simulate(witness, |dr, v| {
        let mut sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
            dr,
            Pasta::circuit_poseidon(params),
        );
        let (v1, v2) = v.cast();
        let allocator = &mut Standard::new();
        let v1 = Element::alloc(dr, allocator, v1)?;
        let v2 = Element::alloc(dr, allocator, v2)?;
        sponge.absorb(dr, &v1)?;
        sponge.absorb(dr, &v2)?;
        let squeezed = sponge.squeeze(dr)?;
        normal_output.set(*squeezed.value().take());
        Ok(())
    })?;

    // Wrong flow: absorb v1, save, resume, absorb v2 (without squeezing first), squeeze.
    // On resume the sponge enters squeeze mode; absorbing without squeezing first
    // switches back to absorb mode mid-stream, producing a different state than
    // the continuous absorb path above.
    Simulator::simulate(witness, |dr, v| {
        let mut sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
            dr,
            Pasta::circuit_poseidon(params),
        );
        let (v1, v2) = v.cast();
        let allocator = &mut Standard::new();
        let v1 = Element::alloc(dr, allocator, v1)?;
        let v2 = Element::alloc(dr, allocator, v2)?;
        sponge.absorb(dr, &v1)?;
        let state = sponge.save_state(dr).expect("save_state should succeed");
        let mut sponge = Sponge::resume(state, Pasta::circuit_poseidon(params));

        // Misuse: absorb before squeezing corrupts the transcript
        sponge.absorb(dr, &v2)?;
        let squeezed = sponge.squeeze(dr)?;
        bad_resume_output.set(*squeezed.value().take());
        Ok(())
    })?;

    // The misuse produces a different hash, demonstrating the bad state.
    assert_ne!(normal_output.get(), bad_resume_output.get());

    Ok(())
}
