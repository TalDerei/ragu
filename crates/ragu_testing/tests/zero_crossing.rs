//! A cheat that drives an `invert`/`divide` input to zero must leave the
//! captured graph unsatisfiable — the gadget's nonzero enforcement
//! (`x · x⁻¹ = 1`) becomes `0 = 1`. The fuzz target turns this into a
//! soundness oracle ("ragu must reject a zeroed divisor"); this test pins
//! the underlying graph behavior deterministically so a regression in the
//! `invert`/`divide` gadgets or the recorder shows up in CI.

use ff::Field;
use ragu_pasta::Fp;
use ragu_testing::{
    recorder::{Recorder, TrackingAllocator, constraints_hold, repair},
    substrate::{Op, Overrides, Preamble, Program, shadow_eval, synthesize},
};

fn preamble() -> Preamble {
    Preamble {
        seeds: [3, 5, 7, 11],
        large_seeds: [[1, 2, 3, 4], [5, 6, 7, 8]],
        special_seeds: [1, 11],
        constant_mask: 0,
    }
}

/// Synthesizes `program`, cheats element advice slot `slot` to zero, and
/// returns whether the repaired captured graph still holds.
fn ragu_accepts_zeroing(program: &Program, slot: usize) -> bool {
    let shadow = shadow_eval::<Fp>(program, Overrides::none());
    let mut rec = Recorder::<Fp>::new();
    let mut alloc = TrackingAllocator::default();
    let stacks = synthesize(&mut rec, &mut alloc, program, &shadow.anchors).unwrap();
    let slot_wires: Vec<usize> = stacks.elems.iter().map(|e| *e.wire()).collect();
    assert!(constraints_hold(&rec.events, &rec.values));

    let mut values = rec.values.clone();
    values[slot_wires[slot]] = Fp::ZERO;
    repair(&rec.events, &mut values, &stacks.advice_wires);
    constraints_hold(&rec.events, &values)
}

#[test]
fn zeroing_an_invert_input_is_rejected() {
    // Allocate a nonzero special value, then invert it. The AllocSpecial
    // element lands at slot `Preamble::LEN`; cheating it to zero must make
    // the captured `x · x⁻¹ = 1` gate unsatisfiable.
    let input_slot = Preamble::LEN;
    let program = Program {
        preamble: preamble(),
        ops: vec![Op::AllocSpecial(7), Op::Invert(input_slot as u8)],
    };
    assert!(
        !ragu_accepts_zeroing(&program, input_slot),
        "ragu accepted a zeroed invert input — nonzero enforcement missing",
    );
}

#[test]
fn zeroing_a_divisor_is_rejected() {
    // Allocate a numerator and a nonzero denominator, then divide. The two
    // AllocSpecial elements land at slots `Preamble::LEN` and `+1`; cheating
    // the divisor to zero must be rejected by `enforce_nonzero`.
    let numerator_slot = Preamble::LEN;
    let divisor_slot = Preamble::LEN + 1;
    let program = Program {
        preamble: preamble(),
        ops: vec![
            Op::AllocSpecial(6),
            Op::AllocSpecial(7),
            Op::Divide(numerator_slot as u8, divisor_slot as u8),
        ],
    };
    assert!(
        !ragu_accepts_zeroing(&program, divisor_slot),
        "ragu accepted a zeroed divisor — enforce_nonzero missing",
    );
}
