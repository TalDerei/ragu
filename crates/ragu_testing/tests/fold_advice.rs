//! Fold scales are prover-controlled advice, not constants. A program with
//! an all-constant preamble plus a single [`Op::Fold`] still has real advice
//! (the scale), and cheating that scale must be *observed* by the patcher
//! differential — routed through the native shadow's
//! [`Overrides::fold_scales`]. Regression for the patcher dropping
//! non-element advice.

use ragu_pasta::Fp;
use ragu_testing::{
    recorder::{Recorder, TrackingAllocator, constraints_hold, repair},
    substrate::{AdviceSlot, Op, Overrides, Preamble, Program, shadow_eval, synthesize},
};

/// All eight preamble slots constant, so the only witness is a later alloc.
fn const_preamble() -> Preamble {
    Preamble {
        seeds: [3, 5, 7, 11],
        large_seeds: [[1, 2, 3, 4], [5, 6, 7, 8]],
        special_seeds: [1, 11],
        constant_mask: 0xFF,
    }
}

/// `Fold(0, 1, s)` over a constant preamble: no element advice, but the
/// scale is advice — and `synth` exposes its wire with the op index.
#[test]
fn fold_scale_is_advice_with_constant_preamble() {
    let program = Program {
        preamble: const_preamble(),
        ops: vec![Op::Fold(0, 1, 9), Op::Anchor(8)],
    };
    let shadow = shadow_eval::<Fp>(&program, Overrides::none());

    let elem_advice = shadow
        .advice
        .iter()
        .filter(|a| matches!(a, AdviceSlot::Elem(_)))
        .count();
    let fold_advice = shadow
        .advice
        .iter()
        .filter(|a| matches!(a, AdviceSlot::FoldScale(_)))
        .count();
    assert_eq!(
        elem_advice, 0,
        "preamble is all-constant: no element advice"
    );
    assert_eq!(fold_advice, 1, "the fold scale is advice");

    let mut rec = Recorder::<Fp>::new();
    let mut alloc = TrackingAllocator::default();
    let stacks = synthesize(&mut rec, &mut alloc, &program, &shadow.anchors).unwrap();
    assert_eq!(
        stacks.fold_advice.len(),
        1,
        "synth exposes the fold scale (op index, wire)",
    );
    assert!(constraints_hold(&rec.events, &rec.values));
}

/// Cheating the fold scale moves the anchored fold result, and the patcher
/// differential (repair vs native shadow through `fold_scales`) agrees on
/// the correctly-constrained circuit — non-vacuously, since the anchor
/// actually moves.
#[test]
fn cheating_a_fold_scale_is_observed_and_sound() {
    let program = Program {
        preamble: const_preamble(),
        ops: vec![Op::Fold(0, 1, 9), Op::Anchor(8)],
    };
    let shadow = shadow_eval::<Fp>(&program, Overrides::none());
    let mut rec = Recorder::<Fp>::new();
    let mut alloc = TrackingAllocator::default();
    let stacks = synthesize(&mut rec, &mut alloc, &program, &shadow.anchors).unwrap();
    let (op_idx, fold_wire) = stacks.fold_advice[0];

    let delta = Fp::from(7u64);

    // ragu side: cheat the fold scale, repair through the captured graph.
    let mut values = rec.values.clone();
    values[fold_wire] += delta;
    repair(&rec.events, &mut values, &stacks.advice_wires);
    let ragu_accepts = constraints_hold(&rec.events, &values);

    // native side: the same cheat, replayed through `fold_scales`.
    let fold_ov = [(op_idx, rec.values[fold_wire] + delta)];
    let mutated = shadow_eval::<Fp>(
        &program,
        Overrides {
            fold_scales: &fold_ov,
            ..Overrides::none()
        },
    );
    let native_ok = mutated.anchors == shadow.anchors;

    assert!(
        !native_ok,
        "the cheat must move the anchored fold result (otherwise vacuous)",
    );
    assert_eq!(
        ragu_accepts, native_ok,
        "fold-scale differential disagreed on a correct circuit",
    );
}
