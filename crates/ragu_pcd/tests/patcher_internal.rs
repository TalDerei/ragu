//! Aiming the patcher engine at the production internal recursion circuits
//! (issue #793).
//!
//! [`Application::capture_internal_circuits`] hands every native internal
//! circuit and its honest witness — which exist only mid-fuse — to a visitor.
//! Here the visitor captures each circuit through the recording driver and
//! checks the capture is faithful two ways:
//!
//! * `constraints_hold` — the [stage overlay](ragu_testing::patcher::overlay_stages)
//!   recovered the honest stage-wire values that `configure_stage` zeros (and
//!   the virtual wires computed from them), so the honest witness satisfies
//!   the recorded graph. This exercises the whole engine on the production
//!   circuits at once: routines (Poseidon permutations), pooled allocation,
//!   and multi-stage reservation.
//! * `playback` — a second, independent synthesis re-accepts the same
//!   witness, so the recording matches a live re-execution rather than merely
//!   agreeing with itself.
//!
//! All five native internal circuits (up to 8527 wires) capture faithfully,
//! which is what a soundness oracle over them needs. Aiming the oracle itself
//! at them additionally requires declaring which of their wires are instance
//! *inputs* — a capture cannot separate those from internal hints through the
//! public API alone — and a worklist solver to keep the sweep affordable on
//! graphs this size.
//!
//! Gated behind `unstable-fuzzing` and run with
//! `cargo test -p ragu_pcd --features unstable-fuzzing`.

use ragu_arithmetic::Cycle;
use ragu_circuits::{Circuit, polynomials::ProductionRank};
use ragu_core::Result;
use ragu_pasta::{Fp, Pasta};
use ragu_pcd::{ApplicationBuilder, patcher::InternalCircuitVisitor};
use ragu_testing::{
    patcher::{capture, constraints_hold, playback},
    pcd::nontrivial::{Hash2, WitnessLeaf},
};
use rand::{SeedableRng, rngs::StdRng};

/// Captures each internal circuit and asserts the capture is faithful.
#[derive(Default)]
struct CaptureChecker {
    visited: usize,
    captured: usize,
}

impl<C: Cycle> InternalCircuitVisitor<C> for CaptureChecker {
    fn visit<'w, Cir: Circuit<C::CircuitField>>(
        &mut self,
        name: &'static str,
        circuit: &Cir,
        make_witness: impl Fn() -> Result<Cir::Witness<'w>>,
    ) -> Result<()> {
        self.visited += 1;
        let cap = capture(circuit, make_witness()?)
            .unwrap_or_else(|e| panic!("{name}: capture must succeed, got {e:?}"));
        assert!(
            constraints_hold(&cap.recorder.events, &cap.recorder.values),
            "{name}: the capture must satisfy the recorded constraints",
        );
        assert!(
            playback(circuit, make_witness()?, cap.recorder.values.clone())?,
            "{name}: an independent playback must re-accept the captured witness",
        );
        self.captured += 1;
        Ok(())
    }
}

/// A real fuse, with the patcher capturing every native internal circuit as
/// its honest witness is built.
#[test]
fn patcher_captures_internal_circuits() -> Result<()> {
    let pasta = Pasta::baked();
    let app = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(WitnessLeaf {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        })?
        .register(Hash2 {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        })?
        .finalize(pasta)?;

    let mut rng = StdRng::seed_from_u64(1234);
    let (leaf1, _) = app.seed(
        &mut rng,
        WitnessLeaf {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        },
        Fp::from(42u64),
    )?;
    let (leaf2, _) = app.seed(
        &mut rng,
        WitnessLeaf {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        },
        Fp::from(42u64),
    )?;

    let mut checker = CaptureChecker::default();
    app.capture_internal_circuits(
        &mut rng,
        Hash2 {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        },
        (),
        leaf1,
        leaf2,
        &mut checker,
    )?;

    assert_eq!(
        checker.visited, 5,
        "all five native internal circuits visited"
    );
    assert_eq!(
        checker.captured, 5,
        "every native internal circuit must capture faithfully",
    );
    Ok(())
}
