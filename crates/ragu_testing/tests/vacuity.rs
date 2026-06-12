//! The anchor tail keeps the patcher differential *observable*.
//!
//! A cheat only generates signal when something downstream notices it:
//! either ragu rejects the repaired witness or a native anchor moves. A
//! random program rarely places anchors downstream of its advice, so most
//! cheats dissolve into unobserved subgraphs and the run is vacuous —
//! both sides accept, the assertion trivially holds, and the fuzz cycle
//! was wasted. [`anchor_tail`] appends anchors on every derived live slot
//! to close that gap.
//!
//! This test measures the vacuous fraction over a fixed corpus, with and
//! without the tail, and pins the improvement so a regression in either
//! `anchor_tail` or the substrate's observability shows up in CI.

use ff::Field;
use ragu_pasta::Fp;
use ragu_testing::{
    recorder::{Recorder, TrackingAllocator, constraints_hold, repair},
    substrate::{
        AdviceSlot, Capabilities, Limits, OpKind, OpSet, Overrides, Program, anchor_tail,
        shadow_eval, synthesize,
    },
};

/// The patcher's repair-safe vocabulary (mirrors `fuzz_advice_patcher`).
fn opset() -> OpSet {
    OpSet::filtered(|k| {
        (k == OpKind::IsZero || !k.capabilities().intersects(Capabilities::BOOLEAN))
            && k != OpKind::AllocRaw
    })
}

/// Deterministic byte stream for corpus generation (splitmix-style LCG).
fn corpus_bytes(seed: u64, len: usize) -> Vec<u8> {
    let mut s = seed;
    (0..len)
        .map(|_| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (s >> 33) as u8
        })
        .collect()
}

/// Runs the standard `+1` cheat on every advice slot of every corpus
/// program and counts `(vacuous, total)` runs. A run is vacuous when no
/// oracle observed the cheat: it bailed on an out-of-model control flip,
/// or both ragu and the native shadow accepted.
fn measure(tail: bool) -> (usize, usize) {
    let (mut vacuous, mut total) = (0usize, 0usize);
    for seed in 1..=40u64 {
        // The preamble alone consumes 99 bytes; the rest become ops.
        let mut program = Program::decode(&corpus_bytes(seed, 256), opset(), Limits::default());
        if program.ops.is_empty() {
            continue;
        }
        if tail {
            program = anchor_tail::<Fp>(&program);
        }
        let shadow = shadow_eval::<Fp>(&program, Overrides::none());
        let advice_slots: Vec<usize> = shadow
            .advice
            .iter()
            .filter_map(|a| match a {
                AdviceSlot::Elem(i) => Some(*i),
                _ => None,
            })
            .collect();

        let mut rec = Recorder::<Fp>::new();
        let mut alloc = TrackingAllocator::default();
        let Ok(stacks) = synthesize(&mut rec, &mut alloc, &program, &shadow.anchors) else {
            continue;
        };
        let slot_wires: Vec<usize> = stacks.elems.iter().map(|e| *e.wire()).collect();
        assert!(constraints_hold(&rec.events, &rec.values));

        for &slot in &advice_slots {
            total += 1;
            let mut vals = rec.values.clone();
            vals[slot_wires[slot]] += Fp::ONE;
            repair(&rec.events, &mut vals, &stacks.advice_wires);
            let ragu_accepts = constraints_hold(&rec.events, &vals);

            let overrides = [(slot, shadow.elems[slot] + Fp::ONE)];
            let mutated = shadow_eval::<Fp>(
                &program,
                Overrides {
                    elems: &overrides,
                    ..Overrides::none()
                },
            );
            let bail = mutated.elems.len() != shadow.elems.len() || mutated.bools != shadow.bools;
            let native_ok = mutated.anchors == shadow.anchors;
            if bail || (ragu_accepts && native_ok) {
                vacuous += 1;
            }
        }
    }
    (vacuous, total)
}

#[test]
fn anchor_tail_keeps_cheats_observed() {
    let (v_plain, t_plain) = measure(false);
    let (v_tail, t_tail) = measure(true);
    println!("vacuous cheats: without tail {v_plain}/{t_plain}, with tail {v_tail}/{t_tail}");

    // Pinned snapshot over the fixed corpus (measured: 300/349 vacuous
    // without the tail, 63/349 with it — a 4.8× improvement). The residue
    // is structural: cheats on *dead* advice that feeds no downstream op
    // (unobservable by any black-box oracle, and free advice that feeds
    // nothing cannot carry a soundness bug) plus zero-crossing bails.
    // Update deliberately, not incidentally.
    assert!(
        v_tail * 5 <= t_tail,
        "anchor tail left {v_tail}/{t_tail} cheats unobserved (>20%)"
    );
    assert!(
        v_tail * t_plain < v_plain * t_tail,
        "anchor tail no longer improves observability \
         (without: {v_plain}/{t_plain}, with: {v_tail}/{t_tail})"
    );
}
