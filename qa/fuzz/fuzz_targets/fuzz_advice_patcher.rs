//! The "patcher" technique with a real repair engine (issues #728, #793).
//!
//! `fuzz_circuit_cheat` is a patcher whose "repair" is re-tracing the
//! circuit on the mutated witness: every wire — including advice — is
//! recomputed by the gadget's own witness logic. That can never expose an
//! under-constrained *advice* wire, because the gadget always recomputes
//! the *correct* advice on a re-run, masking a missing constraint.
//!
//! This target closes that gap. It synthesizes a [`ragu_testing::substrate`]
//! program through a **recording driver** that captures the constraint
//! graph ragu actually emits — every multiplication gate `a·b=c`, every
//! linear-combination wire, every `enforce_zero` — together with the honest
//! wire values. The patcher then mutates one or more *free advice* wires
//! and **repairs through the captured constraints**, not through the gadget
//! logic:
//!
//! * a multiplication gate forces `c := a·b`,
//! * a linear-combination wire is recomputed from its terms,
//! * a copy constraint (`enforce_equal`, the 2-term `enforce_zero` ragu
//!   emits to wire a fresh gate input to an operand) forces the later wire
//!   to equal the earlier one,
//! * every other `enforce_zero` is a *check*, not a repair rule.
//!
//! A fixpoint pass applies those rules until the values stabilise. The
//! result is the witness a malicious prover could submit: it satisfies
//! exactly the constraints ragu emitted, and *only* those.
//!
//! # Vocabulary
//!
//! The repair engine only models `{Lin, Gate, 2-term copy, ≤1-term check}`
//! constraint shapes, so the vocabulary is restricted to the substrate ops
//! that emit *only* those: `OpSet::ALL` minus the boolean ops (which emit
//! 3-term `a + b = 1` enforces and gates the repair engine does not model)
//! and the value-fallible ops (`Invert`/`Divide`/`AllocRaw`, whose
//! inverse-hint constraints are likewise out of model). The free advice the
//! patcher mutates is the element-stack advice (witness inputs,
//! `AllocSpecial`, and `AllocSquare` roots). This is a genuine widening
//! over the historical Add/Sub/Mul/Scale/AllocSquare/Anchor set —
//! `Square`, `Double`, `Negate`, `Fold`, and `AllocConst` now participate.
//!
//! # Mutations
//!
//! A cheat rewrites a free advice wire's value, and the vocabulary targets
//! the corner cases under-constrained bugs live in (see [`Mutation`]):
//! small and full-width additive deltas, exact special values, negation
//! and scaling, and aliasing/swaps against other advice wires — the direct
//! probe for missing copy constraints.
//!
//! # The differential
//!
//! Alongside the captured graph the substrate's native `Fp` shadow knows
//! each gadget's true semantics (the oracle), independent of ragu. For the
//! mutated witness:
//!
//! * `ragu_accepts` — do all captured constraints hold after repair?
//! * `native_satisfied` — does the native shadow, recomputing the full
//!   dependency chain, still satisfy every anchor?
//!
//! The assertion is `ragu_accepts == native_satisfied`. For a correctly
//! constrained circuit the captured-constraint repair and the native
//! recompute agree. **If a gadget omits a constraint, repair fails to
//! propagate the cheat** (there is no captured rule to carry it), so the
//! anchored wire keeps its honest value and ragu accepts, while the native
//! shadow — which knows the true relation — reports the anchor violated.
//! That disagreement is the under-constrained-advice signal.
//!
//! Independently of any cheat, every input also runs the **rank/nullity
//! oracle** (`underconstrained_derived`): the Jacobian of the captured
//! constraints at the honest witness, restricted to the non-free wires,
//! must have a trivial null space — an algebraic, mutation-free detector
//! for wires the constraints fail to pin.
//!
//! The engine — the recording driver, the repair solver, and the planted-bug
//! selftest — lives in `ragu_testing::recorder`, where it is unit tested in
//! CI and reusable against real circuits (issue #793). `PATCHER_SELFTEST=1`
//! runs that selftest here on demand: a deliberately under-constrained
//! circuit (a root and a "square" allocated as independent free wires, with
//! the `square = root²` gate omitted) whose oracle must fire — proof the
//! soundness direction is not vacuous.

#![no_main]

use arbitrary::Arbitrary;
use ff::{Field, PrimeField};
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_testing::{
    recorder::{
        Recorder, TrackingAllocator, constraints_hold, repair, selftest, underconstrained_derived,
    },
    substrate::{
        AdviceSlot, Capabilities, Limits, OpKind, OpSet, Overrides, Program, anchor_tail,
        native_satisfied, shadow_eval, special_value, synthesize,
    },
};
use std::sync::atomic::{AtomicU64, Ordering};

/// Vacuity telemetry (`PATCHER_STATS=1`): a run is *vacuous* when no oracle
/// observed its cheat — it bailed on an out-of-model control flip, or both
/// sides accepted because the cheat dissolved into unobserved freedom. The
/// anchor tail exists to keep this fraction low; if it creeps up, the
/// differential is going soft.
static RUNS: AtomicU64 = AtomicU64::new(0);
/// See [`RUNS`].
static VACUOUS: AtomicU64 = AtomicU64::new(0);

/// Wire-count cap for the rank/nullity oracle: the dense elimination is
/// cubic, so outsized graphs skip it (the cheat differential still runs).
const RANK_WIRE_CAP: usize = 384;

// ---------------------------------------------------------------------------
// Harness.
// ---------------------------------------------------------------------------

/// How a cheat rewrites the honest value of its target advice wire.
///
/// `AddSmall` is the historical mutation, but a `u64` delta explores only a
/// ~2⁻¹⁹⁰ sliver of the field around the honest value, and issue #728's
/// premise is that under-constrained bugs live at corner cases. The rest
/// aim directly at them: exact special values (0, ±1, p−2, 2⁻¹, roots of
/// unity, 2^k boundaries), full-width deltas, sign/scale flips, and
/// aliasing against another advice wire — the direct probe for a missing
/// copy constraint ("these two should both be pinned, but only one is").
#[derive(Arbitrary, Debug, Clone, Copy)]
enum Mutation {
    /// `v + δ` for a small delta `δ ∈ [0, 2⁶⁴)`.
    AddSmall(u64),
    /// `v + δ` for a full-width delta assembled from 32 LE bytes (see
    /// [`wide_value`]).
    AddWide([u8; 32]),
    /// Set to [`special_value`] of the index.
    SetSpecial(u8),
    /// `−v`.
    Negate,
    /// `v · m` for a small factor.
    MulSmall(u64),
    /// Set to the honest value of another advice wire (mod advice count).
    CopyFrom(u16),
    /// Swap honest values with another advice wire — the coordinated form
    /// of [`Mutation::CopyFrom`], moving both wires at once.
    SwapWith(u16),
}

/// A coordinated cheat: which free advice wire (mod advice count) and how
/// to rewrite its value. A run may apply several at once.
#[derive(Arbitrary, Debug, Clone, Copy)]
struct Cheat {
    advice: u16,
    mutation: Mutation,
}

/// Assembles a full-width field element from 32 LE bytes as `lo + hi·2¹²⁸`
/// over the two `u128` halves, covering `[0, 2²⁵⁶) mod p` — deltas the
/// `u64` mutation can never reach.
fn wide_value(bytes: &[u8; 32]) -> Fp {
    let lo = u128::from_le_bytes(bytes[..16].try_into().unwrap());
    let hi = u128::from_le_bytes(bytes[16..].try_into().unwrap());
    let pow128 = Fp::from(1u64 << 63).double().square();
    Fp::from_u128(lo) + Fp::from_u128(hi) * pow128
}

#[derive(Arbitrary, Debug)]
struct Input {
    /// One or more advice wires to mutate simultaneously. Coordinated
    /// multi-wire cheats catch under-constraint that no single-wire change
    /// exposes (e.g. two wires whose product is pinned but neither is).
    cheats: Vec<Cheat>,
    /// Raw program bytes, decoded via [`Program::decode`]. Last field, so
    /// `arbitrary_take_rest` hands it the remainder of the input.
    program: Vec<u8>,
}

/// The repair-safe vocabulary.
///
/// The single-unknown solver (issue #796 item 1) handles any constraint
/// with one unknown, so the value-fallible arithmetic gadgets `invert` and
/// `divide` — whose freshly-allocated inverse/quotient is a *gate input*
/// the solver now back-solves — are in scope (issue #796 item 2), as is
/// `is_zero` (`x·is_zero = 0`, `x·inv = 1 − is_zero`), whose result is
/// regression coverage of those constraint shapes rather than a new oracle
/// (no anchor observes the boolean).
///
/// Excluded: the boolean *combinators* (`BoolAlloc`/`BoolNot`/`BoolAnd`/
/// `ConditionalSelect` — their `a + b = 1` / `a·b = 0` constraints and the
/// complement wire are a separate classification problem, issue #796
/// "later booleans/points/poseidon"), and `AllocRaw` (a non-canonical
/// 32-byte chunk skips its push, and unlike `invert`/`divide` that skip
/// depends on fuzzer bytes, not a mutatable value, so the progression guard
/// below cannot neutralize it).
///
/// # Value-dependent solvability (guarded in the harness)
///
/// `invert`/`divide` *skip* when their honest input is zero, so they are
/// simply absent from the honest graph (Recorder and shadow skip
/// identically). `is_zero` never skips, but its inverse hint `inv` becomes
/// a genuinely free wire when `x = 0` (the gate `0·inv = is_not_zero` has
/// two unknowns the single-unknown solver cannot crack). In both cases a
/// *cheat* that moves such an input across zero changes either the native
/// shadow's stack progression (`invert`/`divide`) or a boolean result
/// (`is_zero`); the harness bails on both — those value-dependent control
/// flips are outside this model and would otherwise be false positives.
fn opset() -> OpSet {
    OpSet::filtered(|k| {
        (k == OpKind::IsZero || !k.capabilities().intersects(Capabilities::BOOLEAN))
            && k != OpKind::AllocRaw
    })
}

fuzz_target!(|input: Input| {
    if std::env::var("PATCHER_SELFTEST").is_ok() {
        selftest::<Fp>();
        return;
    }

    let program = Program::decode(&input.program, opset(), Limits::default());

    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!("cheats = {:?}\n{program:#?}", input.cheats);
        return;
    }
    if program.ops.is_empty() {
        return;
    }

    // Maximize observability: anchor every derived slot the honest run
    // leaves live, so a cheat that propagates anywhere is observed by some
    // anchor (advice slots stay unanchored — see `anchor_tail`).
    let program = anchor_tail::<Fp>(&program);

    // Honest native shadow: correct semantics, anchor observations, and the
    // free-advice inventory. Element-stack advice (witness inputs,
    // AllocSpecial, AllocSquare roots) are the mutation targets.
    let shadow = shadow_eval::<Fp>(&program, Overrides::none());
    let honest_anchors = shadow.anchors.clone();
    let advice_slots: Vec<usize> = shadow
        .advice
        .iter()
        .filter_map(|a| match a {
            AdviceSlot::Elem(i) => Some(*i),
            _ => None,
        })
        .collect();
    if advice_slots.is_empty() {
        return;
    }

    // Capture the honest constraint graph and per-slot wire ids.
    let mut rec = Recorder::<Fp>::new();
    let mut alloc = TrackingAllocator::default();
    let stacks = match synthesize(&mut rec, &mut alloc, &program, &honest_anchors) {
        Ok(s) => s,
        Err(_) => return,
    };
    let slot_wires: Vec<usize> = stacks.elems.iter().map(|e| *e.wire()).collect();

    // Completeness: the honest witness satisfies the captured constraints
    // and the native oracle agrees. Both hold by construction.
    assert!(
        constraints_hold(&rec.events, &rec.values),
        "honest witness violated a captured constraint (harness bug): {program:?}"
    );
    assert!(
        native_satisfied(&program, &honest_anchors, Overrides::none()),
        "honest native oracle disagreed with itself (harness bug): {program:?}"
    );

    // Rank/nullity oracle, independent of any cheat: with the genuine free
    // wires (advice, gate-D extras, allocator waste) held fixed, every
    // remaining wire must be locally pinned by the captured constraints.
    // Skipped when an honest is_zero input was zero — its inverse hint is
    // genuinely (and benignly) free there — and on outsized graphs.
    if rec.values.len() <= RANK_WIRE_CAP && !shadow.bools.iter().any(|&b| b) {
        let mut rank_free = stacks.advice_wires.clone();
        rank_free.extend_from_slice(&rec.extras);
        rank_free.extend_from_slice(&alloc.wasted);
        let movable = underconstrained_derived(&rec.events, &rec.values, &rank_free);
        assert!(
            movable.is_empty(),
            "RANK ORACLE SIGNAL: derived wires {movable:?} can move while every \
             free wire is held fixed — an under-constrained wire, found \
             algebraically (no cheat, repair, or anchor needed). Program: {program:?}",
        );
    }

    // Resolve the coordinated cheat into (advice slot, new value) pairs,
    // deduplicated by slot so a wire is mutated at most once (first cheat
    // wins, including the second leg of a swap). A run with no cheats is
    // degenerate; default to a single cheat on the first advice wire so
    // every input does some work.
    let raw_cheats = if input.cheats.is_empty() {
        vec![Cheat {
            advice: 0,
            mutation: Mutation::AddSmall(1),
        }]
    } else {
        input.cheats.clone()
    };
    let mut slot_value: Vec<(usize, Fp)> = Vec::new();
    for ch in &raw_cheats {
        let slot = advice_slots[ch.advice as usize % advice_slots.len()];
        if slot_value.iter().any(|(s, _)| *s == slot) {
            continue;
        }
        let honest = shadow.elems[slot];
        let other = |o: u16| advice_slots[o as usize % advice_slots.len()];
        let value = match ch.mutation {
            Mutation::AddSmall(d) => honest + Fp::from(d),
            Mutation::AddWide(b) => honest + wide_value(&b),
            Mutation::SetSpecial(i) => special_value(i),
            Mutation::Negate => -honest,
            Mutation::MulSmall(m) => honest * Fp::from(m),
            Mutation::CopyFrom(o) => shadow.elems[other(o)],
            Mutation::SwapWith(o) => {
                let other_slot = other(o);
                if other_slot != slot && !slot_value.iter().any(|(s, _)| *s == other_slot) {
                    slot_value.push((other_slot, honest));
                }
                shadow.elems[other_slot]
            }
        };
        slot_value.push((slot, value));
    }
    // Every cheat must do work: a mutation that lands back on the honest
    // value (zero delta, ×1, copy between equal wires, …) is nudged off it.
    for (slot, value) in &mut slot_value {
        if *value == shadow.elems[*slot] {
            *value += Fp::ONE;
        }
    }

    // ragu side: apply the cheats, then solve the captured graph for the
    // witness — in the *accomplice* adversary model. Only the cheated
    // element advice and the non-element advice (fold scales, booleans)
    // are held fixed; every *non-cheated* element-advice wire is left
    // solvable, modeling a prover who adjusts its other advice to mask the
    // cheat. The solver picks those accomplice values, and we feed them
    // back to the native oracle below so both judge the *same* commitment.
    let cheated_slots: Vec<usize> = slot_value.iter().map(|(s, _)| *s).collect();
    let accomplice_wires: Vec<usize> = advice_slots
        .iter()
        .filter(|s| !cheated_slots.contains(s))
        .map(|s| slot_wires[*s])
        .collect();
    let fixed_free: Vec<usize> = stacks
        .advice_wires
        .iter()
        .copied()
        .filter(|w| !accomplice_wires.contains(w))
        .collect();

    let mut ragu_values = rec.values.clone();
    for (slot, value) in &slot_value {
        ragu_values[slot_wires[*slot]] = *value;
    }
    repair(&rec.events, &mut ragu_values, &fixed_free);
    let ragu_accepts = constraints_hold(&rec.events, &ragu_values);

    // native side: judge the exact commitment ragu accepted — the cheats
    // *and* the accomplice advice the solver chose. Each element-advice slot
    // is overridden to its post-repair value; derived wires the shadow
    // recomputes itself from true semantics.
    let elem_overrides: Vec<(usize, Fp)> = advice_slots
        .iter()
        .map(|s| (*s, ragu_values[slot_wires[*s]]))
        .collect();
    let mutated = shadow_eval::<Fp>(
        &program,
        Overrides {
            elems: &elem_overrides,
            ..Overrides::none()
        },
    );

    // Value-dependent-solvability guard (see `opset`). Two out-of-model
    // flips, both caused by a cheat moving a gadget input across zero:
    //
    //  * `invert`/`divide` skip in the native re-evaluation, shifting every
    //    later stack slot — detected by a change in element-stack length;
    //  * an `is_zero` result flips, which is exactly when its inverse hint
    //    becomes a free wire the single-unknown solver cannot re-derive —
    //    detected by a change in the boolean stack.
    //
    // In both cases the captured graph (fixed from the honest run) and the
    // shifted shadow are incomparable, so bail rather than emit a spurious
    // signal. The honest graph never skips or flips, so this only fires for
    // genuinely value-flipping cheats.
    let bail = mutated.elems.len() != shadow.elems.len() || mutated.bools != shadow.bools;
    let native_ok = mutated.anchors == honest_anchors;

    if std::env::var("PATCHER_STATS").is_ok() {
        let runs = RUNS.fetch_add(1, Ordering::Relaxed) + 1;
        if bail || (ragu_accepts && native_ok) {
            VACUOUS.fetch_add(1, Ordering::Relaxed);
        }
        if runs % (1 << 14) == 0 {
            eprintln!(
                "[advice_patcher] vacuous {}/{runs} runs",
                VACUOUS.load(Ordering::Relaxed),
            );
        }
    }
    if bail {
        return;
    }

    assert_eq!(
        ragu_accepts,
        native_ok,
        "PATCHER SOUNDNESS SIGNAL: setting advice (slot, value) {slot_value:?} \
         and repairing through the captured constraints, ragu {} the witness \
         but the native oracle says it is {}. {}. Program: {program:?}",
        if ragu_accepts { "ACCEPTED" } else { "REJECTED" },
        if native_ok { "satisfied" } else { "VIOLATED" },
        if ragu_accepts && !native_ok {
            "ragu accepted a witness the oracle rejects — an under-constrained advice wire \
             (the soundness direction)"
        } else {
            "ragu rejected a witness the oracle accepts — a completeness gap"
        },
    );
});
