//! The playback driver re-derives the patcher's accept/reject verdict from
//! a fresh synthesis of the real gadget calls, independently of the
//! recorder's stored constraint graph. This test pins two properties:
//!
//! 1. **Agreement with ragu.** On the honest witness, playback accepts
//!    exactly when ragu's own [`Simulator`] accepts — tying playback's
//!    notion of satisfaction to the real driver.
//! 2. **It catches a corrupted graph.** If the recorder's stored events are
//!    tampered with (a dropped constraint), the recorder's verdict and the
//!    playback's verdict diverge — which is the whole point of the
//!    cross-check.

use ff::Field;
use proptest::prelude::*;
use ragu_pasta::Fp;
use ragu_primitives::{Simulator, allocator::Standard};
use ragu_testing::{
    recorder::{Event, Playback, Recorder, TrackingAllocator, constraints_hold, repair},
    substrate::{
        Limits, OpSet, Overrides, Preamble, Program, program_strategy, shadow_eval, synthesize,
    },
};

/// Whether a single captured event holds at `values` — the per-event body
/// of [`constraints_hold`], used to locate the violated constraint.
fn single_event_holds(ev: &Event<Fp>, values: &[Fp]) -> bool {
    match ev {
        Event::Lin { out, terms } => {
            values[*out] == terms.iter().map(|(w, c)| values[*w] * c).sum()
        }
        Event::Gate { a, b, c } => values[*a] * values[*b] == values[*c],
        Event::Enforce { terms } => {
            terms.iter().map(|(w, c)| values[*w] * c).sum::<Fp>() == Fp::ZERO
        }
    }
}

fn preamble() -> Preamble {
    Preamble {
        seeds: [3, 5, 7, 11],
        large_seeds: [[1, 2, 3, 4], [5, 6, 7, 8]],
        special_seeds: [1, 11],
        constant_mask: 0b0000_0101,
    }
}

/// On the honest witness, playback and ragu's `Simulator` agree (both
/// accept), and playback consumes exactly the recorder's wires.
#[test]
fn playback_agrees_with_simulator_on_honest_witness() {
    let program = Program {
        preamble: preamble(),
        ops: vec![
            ragu_testing::substrate::Op::Add(0, 1),
            ragu_testing::substrate::Op::Mul(8, 2),
            ragu_testing::substrate::Op::AllocSquare(9),
            ragu_testing::substrate::Op::Anchor(8),
        ],
    };
    let shadow = shadow_eval::<Fp>(&program, Overrides::none());

    // Recorder captures the honest graph and values.
    let mut rec = Recorder::<Fp>::new();
    let mut alloc = TrackingAllocator::default();
    synthesize(&mut rec, &mut alloc, &program, &shadow.anchors).unwrap();

    // ragu's real Simulator accepts the honest witness.
    let sim = Simulator::<Fp>::simulate((), |dr, _| {
        synthesize(dr, &mut Standard::new(), &program, &shadow.anchors)?;
        Ok(())
    });
    assert!(sim.is_ok(), "Simulator rejected the honest witness");

    // Playback over the recorder's honest values accepts and agrees.
    let mut playback = Playback::new(rec.values.clone());
    synthesize(&mut playback, &mut (), &program, &shadow.anchors).unwrap();
    assert!(playback.accepts(), "playback rejected the honest witness");
    assert!(constraints_hold(&rec.events, &rec.values));
}

/// If the recorder's stored graph is corrupted (a constraint dropped), its
/// verdict no longer matches the playback re-execution — the cross-check
/// fires. This is the fuzz target's `RECORDER CAPTURE BUG` assertion in
/// miniature, with the corruption injected by hand.
#[test]
fn playback_catches_a_dropped_constraint() {
    // A simple multiply-and-anchor circuit; cheat an input so the honest
    // anchor is violated, which a faithful graph rejects.
    let program = Program {
        preamble: preamble(),
        ops: vec![
            ragu_testing::substrate::Op::Mul(0, 1),
            ragu_testing::substrate::Op::Anchor(8),
        ],
    };
    let shadow = shadow_eval::<Fp>(&program, Overrides::none());
    let mut rec = Recorder::<Fp>::new();
    let mut alloc = TrackingAllocator::default();
    let stacks = synthesize(&mut rec, &mut alloc, &program, &shadow.anchors).unwrap();

    // Cheat the first advice wire and repair.
    let mut values = rec.values.clone();
    values[stacks.advice_wires[0]] += Fp::ONE;
    repair(&rec.events, &mut values, &stacks.advice_wires);

    let faithful = constraints_hold(&rec.events, &values);
    assert!(!faithful, "the cheat should violate the anchor");

    // Playback (faithful re-execution of the real gadget calls) agrees with
    // the faithful stored graph.
    let mut playback = Playback::new(values.clone());
    synthesize(&mut playback, &mut (), &program, &shadow.anchors).unwrap();
    assert_eq!(
        playback.accepts(),
        faithful,
        "playback diverged from the faithful graph",
    );

    // Corrupt the stored graph by dropping the violated constraint, so it
    // now (wrongly) accepts. Playback, which re-executes the real circuit,
    // still rejects — the divergence the fuzz cross-check flags.
    let violated = rec
        .events
        .iter()
        .position(|e| !single_event_holds(e, &values))
        .expect("some constraint must be violated");
    let mut corrupted = rec.events.clone();
    corrupted.remove(violated);
    let corrupted_verdict = constraints_hold(&corrupted, &values);
    assert!(
        corrupted_verdict,
        "dropping the only violated constraint should make the graph accept",
    );
    assert_ne!(
        playback.accepts(),
        corrupted_verdict,
        "playback must disagree with the corrupted graph",
    );
}

proptest! {
    /// Over random programs and random witnesses, the recorder's stored
    /// verdict and the playback re-execution always agree — the recorder
    /// faithfully captures the gadget calls.
    #[test]
    fn proptest_recorder_matches_playback(
        program in program_strategy(
            OpSet::ALL.without(ragu_testing::substrate::Capabilities::VALUE_FALLIBLE),
            Limits::default().max_ops,
        ),
        perturb in proptest::collection::vec(0u64..5, 0..8),
    ) {
        let shadow = shadow_eval::<Fp>(&program, Overrides::none());
        let mut rec = Recorder::<Fp>::new();
        let mut alloc = TrackingAllocator::default();
        let stacks = match synthesize(&mut rec, &mut alloc, &program, &shadow.anchors) {
            Ok(s) => s,
            Err(_) => return Ok(()),
        };

        // Apply an arbitrary perturbation to some advice wires, then repair
        // — exercising both accepting and rejecting witnesses.
        let mut values = rec.values.clone();
        for (i, p) in perturb.iter().enumerate() {
            if !stacks.advice_wires.is_empty() {
                let w = stacks.advice_wires[i % stacks.advice_wires.len()];
                values[w] += Fp::from(*p);
            }
        }
        repair(&rec.events, &mut values, &stacks.advice_wires);
        let stored = constraints_hold(&rec.events, &values);

        let mut playback = Playback::new(values.clone());
        if synthesize(&mut playback, &mut (), &program, &shadow.anchors).is_ok() {
            prop_assert_eq!(
                playback.accepts(),
                stored,
                "recorder/playback disagree on {:?}",
                program,
            );
        }
    }
}
