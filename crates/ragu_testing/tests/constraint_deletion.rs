//! Mutation-testing the patcher's detectors: delete each captured
//! constraint and check that an oracle notices (issue #728's evaluation
//! methodology, applied to our own engine).
//!
//! For every `Gate` / `Enforce` event a generated program emits, this
//! benchmark removes that one event — modeling a gadget that forgot to
//! emit it — and classifies the result:
//!
//! * **RankHit** — [`underconstrained_derived`] reports a movable derived
//!   wire. Fires even when nothing observes the wire.
//! * **CheatHit** — the rank oracle is quiet, but a single-advice cheat,
//!   repaired through the weakened graph, is accepted by ragu while the
//!   native shadow reports an anchor violated. This is the differential's
//!   bug class: a wire still *pinned*, but to the wrong thing.
//! * **Redundant** — deleting the event does not reduce the rank of the
//!   full Jacobian (advice directions included): the remaining constraints
//!   already enforce everything it did, so there is nothing to detect.
//!   Allocation gates (`a·0 = 0`) are the common case.
//! * **Blind** — the deletion lost a real pin and no oracle fired: either
//!   the freed direction reaches no anchor (unobservable — more anchors is
//!   the fix, see the anchor-steering work) or it needs a coordinated
//!   multi-wire cheat the search does not attempt.
//!
//! The per-category counts over a fixed, deterministic corpus are pinned
//! below. The pin is the regression guard: a solver or oracle change that
//! silently loses sensitivity shifts hits toward Blind and fails the test.
//! If you *improve* the engine (fewer Blind), update the pin downward and
//! celebrate.

use ff::Field;
use ragu_pasta::Fp;
use ragu_testing::{
    recorder::{
        Event, Recorder, TrackingAllocator, constraints_hold, derived_rank, repair,
        underconstrained_derived,
    },
    substrate::{
        AdviceSlot, Capabilities, Limits, OpKind, OpSet, Overrides, Preamble, Program, shadow_eval,
        synthesize,
    },
};

/// The patcher's repair-safe vocabulary (mirrors `fuzz_advice_patcher`).
fn opset() -> OpSet {
    OpSet::filtered(|k| {
        (k == OpKind::IsZero || !k.capabilities().intersects(Capabilities::BOOLEAN))
            && k != OpKind::AllocRaw
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Verdict {
    RankHit,
    CheatHit,
    Redundant,
    Blind,
}

#[derive(Default, Debug, PartialEq, Eq)]
struct Stats {
    rank: usize,
    cheat: usize,
    redundant: usize,
    blind: usize,
}

/// Everything the classifier needs about one honest synthesis.
struct Fixture {
    program: Program,
    events: Vec<Event<Fp>>,
    values: Vec<Fp>,
    /// The prover's genuine degrees of freedom (advice wires).
    advice_wires: Vec<usize>,
    /// Exempt-but-not-advice wires: gate-D extras and allocator waste.
    exempt: Vec<usize>,
    /// Element-stack slot -> recorder wire.
    slot_wires: Vec<usize>,
    /// Element-stack advice slots (the cheat search's targets).
    advice_slots: Vec<usize>,
    /// The honest shadow (anchor observations, stack shapes).
    honest_elems: Vec<Fp>,
    honest_bools: Vec<bool>,
    honest_anchors: Vec<Fp>,
}

/// Synthesizes `program` through the recorder; `None` for degenerate
/// programs (no ops, no advice, an honest `is_zero` of zero, or synthesis
/// failure).
fn fixture(program: Program) -> Option<Fixture> {
    if program.ops.is_empty() {
        return None;
    }
    let shadow = shadow_eval::<Fp>(&program, Overrides::none());
    // An honest zero into is_zero leaves its inverse hint genuinely free,
    // which the rank oracle would (correctly but unhelpfully) report.
    if shadow.bools.iter().any(|&b| b) {
        return None;
    }
    let advice_slots: Vec<usize> = shadow
        .advice
        .iter()
        .filter_map(|a| match a {
            AdviceSlot::Elem(i) => Some(*i),
            _ => None,
        })
        .collect();
    if advice_slots.is_empty() {
        return None;
    }

    let mut rec = Recorder::<Fp>::new();
    let mut alloc = TrackingAllocator::default();
    let stacks = synthesize(&mut rec, &mut alloc, &program, &shadow.anchors).ok()?;
    let slot_wires: Vec<usize> = stacks.elems.iter().map(|e| *e.wire()).collect();

    let mut exempt = rec.extras.clone();
    exempt.extend_from_slice(&alloc.wasted);

    assert!(
        constraints_hold(&rec.events, &rec.values),
        "honest witness violated a captured constraint (harness bug)",
    );

    Some(Fixture {
        program,
        events: rec.events,
        values: rec.values,
        advice_wires: stacks.advice_wires,
        exempt,
        slot_wires,
        advice_slots,
        honest_elems: shadow.elems,
        honest_bools: shadow.bools,
        honest_anchors: shadow.anchors,
    })
}

impl Fixture {
    fn free(&self) -> Vec<usize> {
        let mut free = self.advice_wires.clone();
        free.extend_from_slice(&self.exempt);
        free
    }

    /// Classifies the deletion of `self.events[i]`.
    fn classify(&self, i: usize) -> Verdict {
        let mut weakened = self.events.clone();
        weakened.remove(i);
        let free = self.free();

        // (1) Rank oracle: a derived wire came unpinned.
        if !underconstrained_derived(&weakened, &self.values, &free).is_empty() {
            return Verdict::RankHit;
        }

        // (2) Cheat search: single-advice cheats through the weakened graph.
        let deltas = [Fp::ONE, Fp::from(7u64), -Fp::ONE];
        for &slot in &self.advice_slots {
            for delta in deltas {
                let mut vals = self.values.clone();
                vals[self.slot_wires[slot]] += delta;
                repair(&weakened, &mut vals, &self.advice_wires);
                if !constraints_hold(&weakened, &vals) {
                    continue; // the weakened graph still rejects this cheat
                }
                let overrides = [(slot, self.honest_elems[slot] + delta)];
                let mutated = shadow_eval::<Fp>(
                    &self.program,
                    Overrides {
                        elems: &overrides,
                        ..Overrides::none()
                    },
                );
                // Out-of-model control flips (see the fuzz target's guard).
                if mutated.elems.len() != self.honest_elems.len()
                    || mutated.bools != self.honest_bools
                {
                    continue;
                }
                if mutated.anchors != self.honest_anchors {
                    return Verdict::CheatHit;
                }
            }
        }

        // (3) Redundant vs blind: did the deletion lose a real pin on the
        // full Jacobian (advice directions included)?
        let before = derived_rank(&self.events, &self.values, &self.exempt);
        let after = derived_rank(&weakened, &self.values, &self.exempt);
        if after == before {
            Verdict::Redundant
        } else {
            Verdict::Blind
        }
    }

    /// Classifies every `Gate`/`Enforce` deletion (Lin events are wire
    /// *definitions*, not constraints a gadget could forget to emit).
    fn run(&self, stats: &mut Stats) {
        for i in 0..self.events.len() {
            if matches!(self.events[i], Event::Lin { .. }) {
                continue;
            }
            match self.classify(i) {
                Verdict::RankHit => stats.rank += 1,
                Verdict::CheatHit => stats.cheat += 1,
                Verdict::Redundant => stats.redundant += 1,
                Verdict::Blind => stats.blind += 1,
            }
        }
    }
}

fn test_preamble() -> Preamble {
    Preamble {
        seeds: [3, 5, 7, 11],
        large_seeds: [[1, 2, 3, 4], [5, 6, 7, 8]],
        special_seeds: [1, 11],
        constant_mask: 0,
    }
}

/// A handcrafted, fully classified program: a multiplied-and-anchored pair
/// plus an unanchored square. Every deletion must be detected or provably
/// redundant — zero blind spots — and both detectors must contribute.
#[test]
fn handcrafted_deletions_all_detected() {
    use ragu_testing::substrate::Op;

    let program = Program {
        preamble: test_preamble(),
        ops: vec![Op::Mul(0, 1), Op::Anchor(8), Op::Square(2)],
    };
    let fixture = fixture(program).expect("handcrafted fixture must build");
    let mut stats = Stats::default();
    fixture.run(&mut stats);

    assert_eq!(
        stats.blind, 0,
        "blind deletions in a fully observed program: {stats:?}"
    );
    assert!(stats.rank > 0, "the rank oracle never fired: {stats:?}");
    assert!(stats.cheat > 0, "the cheat search never fired: {stats:?}");
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

/// The pinned sensitivity snapshot over a fixed generated corpus.
///
/// These counts are deterministic. A change that *reduces* sensitivity
/// (hits shifting into Blind) fails here and needs a deliberate decision;
/// a change that improves it updates the pin downward.
#[test]
fn corpus_deletion_sensitivity() {
    let mut stats = Stats::default();
    let mut programs = 0;
    for seed in 1..=24u64 {
        // The preamble alone consumes 99 bytes; the rest become ops.
        let program = Program::decode(&corpus_bytes(seed, 256), opset(), Limits::default());
        let Some(fixture) = fixture(program) else {
            continue;
        };
        programs += 1;
        fixture.run(&mut stats);
    }

    let total = stats.rank + stats.cheat + stats.redundant + stats.blind;
    println!(
        "constraint-deletion sensitivity over {programs} programs, \
         {total} deletions: {stats:?}"
    );
    assert!(
        programs >= 10,
        "corpus degenerated: only {programs} programs"
    );

    // The pinned snapshot: 99.9% of non-redundant deletions detected (1 of
    // 1508 blind). The linear-cluster solver moved 10 deletions out of Blind
    // (was 11) by repairing coupled 2-unknown clusters the single-unknown
    // solver stalled on; the lone remaining blind spot needs a coordinated
    // multi-wire cheat the single-advice search does not attempt.
    // Update deliberately, not incidentally.
    assert_eq!(
        stats,
        Stats {
            rank: 1474,
            cheat: 33,
            redundant: 272,
            blind: 1,
        },
        "sensitivity snapshot changed",
    );
}
