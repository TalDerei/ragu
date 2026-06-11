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
//! `PATCHER_SELFTEST=1` builds a deliberately under-constrained circuit
//! directly in the recorder (a root and a "square" allocated as independent
//! free wires, with the `square = root²` gate omitted) and confirms the
//! oracle fires — proof the soundness direction is not vacuous.

#![no_main]

use arbitrary::Arbitrary;
use ff::Field;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_arithmetic::Coeff;
use ragu_core::{
    Result as RaguResult,
    drivers::{Driver, DriverTypes, LinearExpression},
    gadgets::Bound,
    maybe::Always,
    routines::Routine,
};
use ragu_testing::substrate::{
    AdviceSlot, Capabilities, Limits, OpSet, Overrides, Program, native_satisfied, shadow_eval,
    synthesize,
};

// ---------------------------------------------------------------------------
// Recording driver: captures the constraint graph ragu emits.
// ---------------------------------------------------------------------------

/// A captured constraint / wire definition, in emission order.
#[derive(Clone, Debug)]
enum Ev {
    /// `out` is a virtual wire equal to `Σ coeff · wire` over `terms`.
    Lin { out: usize, terms: Vec<(usize, Fp)> },
    /// A multiplication gate: `values[a] · values[b] == values[c]`.
    Gate { a: usize, b: usize, c: usize },
    /// A constraint `Σ coeff · wire == 0` over `terms`.
    Enforce { terms: Vec<(usize, Fp)> },
}

/// The recording driver. `Wire = usize`, an index into `values`.
struct Recorder {
    values: Vec<Fp>,
    events: Vec<Ev>,
}

impl Recorder {
    fn new() -> Self {
        // Wire 0 is the fixed ONE wire.
        Recorder {
            values: vec![Fp::ONE],
            events: Vec::new(),
        }
    }

    fn push_wire(&mut self, value: Fp) -> usize {
        let id = self.values.len();
        self.values.push(value);
        id
    }
}

/// Recording linear expression: accumulates `(wire, resolved_coeff)` terms,
/// folding the running gain into each coefficient as it is added. It records
/// only structure; the driver computes the resulting value from its own
/// wire table afterwards.
struct RecLc {
    terms: Vec<(usize, Fp)>,
    gain: Fp,
}

impl Default for RecLc {
    fn default() -> Self {
        RecLc {
            terms: Vec::new(),
            gain: Fp::ONE,
        }
    }
}

impl LinearExpression<usize, Fp> for RecLc {
    fn add_term(mut self, wire: &usize, coeff: Coeff<Fp>) -> Self {
        let resolved = coeff.value() * self.gain;
        if resolved != Fp::ZERO {
            self.terms.push((*wire, resolved));
        }
        self
    }

    fn gain(mut self, coeff: Coeff<Fp>) -> Self {
        self.gain *= coeff.value();
        self
    }
}

impl DriverTypes for Recorder {
    type ImplField = Fp;
    type ImplWire = usize;
    type MaybeKind = Always<()>;
    type LCadd = RecLc;
    type LCenforce = RecLc;
    type Extra = ();

    fn gate(
        &mut self,
        values: impl Fn() -> RaguResult<(Coeff<Fp>, Coeff<Fp>, Coeff<Fp>)>,
    ) -> RaguResult<(usize, usize, usize, ())> {
        let (a, b, c) = values()?;
        let (a, b, c) = (a.value(), b.value(), c.value());
        let ia = self.push_wire(a);
        let ib = self.push_wire(b);
        let ic = self.push_wire(c);
        self.events.push(Ev::Gate {
            a: ia,
            b: ib,
            c: ic,
        });
        Ok((ia, ib, ic, ()))
    }

    fn assign_extra(
        &mut self,
        _extra: (),
        value: impl Fn() -> RaguResult<Coeff<Fp>>,
    ) -> RaguResult<usize> {
        let v = value()?.value();
        Ok(self.push_wire(v))
    }
}

impl<'dr> Driver<'dr> for Recorder {
    type F = Fp;
    type Wire = usize;
    const ONE: usize = 0;

    fn add(&mut self, lc: impl Fn(RecLc) -> RecLc) -> usize {
        let built = lc(RecLc::default());
        let value = built.terms.iter().map(|(w, c)| self.values[*w] * c).sum();
        let out = self.push_wire(value);
        self.events.push(Ev::Lin {
            out,
            terms: built.terms,
        });
        out
    }

    fn enforce_zero(&mut self, lc: impl Fn(RecLc) -> RecLc) -> RaguResult<()> {
        let built = lc(RecLc::default());
        self.events.push(Ev::Enforce { terms: built.terms });
        Ok(())
    }

    fn routine<R: Routine<Fp> + 'dr>(
        &mut self,
        _routine: R,
        _input: Bound<'dr, Self, R::Input>,
    ) -> RaguResult<Bound<'dr, Self, R::Output>> {
        unreachable!("the advice-patcher substrate never invokes routines")
    }
}

// ---------------------------------------------------------------------------
// Repair engine: propagate a mutation through the *captured* constraints.
// ---------------------------------------------------------------------------

/// Apply the captured constraint rules to `values` to a fixpoint, never
/// overwriting any wire in `frozen` (the mutation targets):
/// * `Lin`  → recompute the virtual wire from its terms,
/// * `Gate` → force `c := a·b`,
/// * 2-term `Enforce` (`c1·w1 + c2·w2 == 0`) → force the *later* wire.
///
/// Other `Enforce` events are checks, applied later, not here.
fn repair(events: &[Ev], values: &mut [Fp], frozen: &[usize]) {
    let is_frozen = |w: usize| frozen.contains(&w);
    for _ in 0..(events.len() + 2) {
        let mut changed = false;
        for ev in events {
            match ev {
                Ev::Lin { out, terms } => {
                    if is_frozen(*out) {
                        continue;
                    }
                    let v = terms.iter().map(|(w, c)| values[*w] * c).sum();
                    if values[*out] != v {
                        values[*out] = v;
                        changed = true;
                    }
                }
                Ev::Gate { a, b, c } => {
                    if is_frozen(*c) {
                        continue;
                    }
                    let v = values[*a] * values[*b];
                    if values[*c] != v {
                        values[*c] = v;
                        changed = true;
                    }
                }
                Ev::Enforce { terms } => {
                    // Treat a clean 2-term constraint as a copy that defines
                    // the later-created wire; everything else is a check.
                    if terms.len() == 2 {
                        let (w1, c1) = terms[0];
                        let (w2, c2) = terms[1];
                        let (lo, hi, c_lo, c_hi) = if w1 < w2 {
                            (w1, w2, c1, c2)
                        } else {
                            (w2, w1, c2, c1)
                        };
                        if is_frozen(hi) || c_hi == Fp::ZERO {
                            continue;
                        }
                        // c_hi·v_hi + c_lo·v_lo = 0  ⇒  v_hi = -(c_lo/c_hi)·v_lo
                        let v = -(c_lo * c_hi.invert().unwrap()) * values[lo];
                        if values[hi] != v {
                            values[hi] = v;
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
}

/// After repair, do all captured constraints hold?
fn constraints_hold(events: &[Ev], values: &[Fp]) -> bool {
    events.iter().all(|ev| match ev {
        Ev::Lin { out, terms } => values[*out] == terms.iter().map(|(w, c)| values[*w] * c).sum(),
        Ev::Gate { a, b, c } => values[*a] * values[*b] == values[*c],
        Ev::Enforce { terms } => terms.iter().map(|(w, c)| values[*w] * c).sum::<Fp>() == Fp::ZERO,
    })
}

// ---------------------------------------------------------------------------
// Harness.
// ---------------------------------------------------------------------------

/// A coordinated cheat: which free advice wire (mod advice count) and the
/// nonzero delta to add. A run may apply several at once.
#[derive(Arbitrary, Debug, Clone, Copy)]
struct Cheat {
    advice: u16,
    delta: u64,
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

/// The repair-safe vocabulary: ops emitting only `{Lin, Gate, 2-term copy,
/// ≤1-term check}` constraints. Booleans (3-term `a+b=1` enforces) and
/// value-fallible ops (inverse-hint constraints) are out of the repair
/// engine's model.
fn opset() -> OpSet {
    OpSet::ALL
        .without(Capabilities::BOOLEAN)
        .without(Capabilities::VALUE_FALLIBLE)
}

/// `PATCHER_SELFTEST=1`: build a deliberately under-constrained circuit in
/// the recorder and confirm the patcher's soundness assertion fires.
///
/// The circuit allocates `root` and `square` as independent free wires and
/// anchors `square` to its honest value `root²`, but omits the
/// `square = root²` gate. Mutating `root` and repairing through the
/// captured constraints leaves `square` untouched (no rule carries the
/// change), so ragu accepts — while the true semantics say `square` must
/// move, violating the anchor. The mismatch is the signal.
fn run_selftest() {
    let root_honest = Fp::from(7u64);

    let mut rec = Recorder::new();
    let root = rec.push_wire(root_honest); // free advice
    let square = rec.push_wire(root_honest.square()); // free advice — BUG: not gated to root²

    // Anchor `square` to its honest value via `enforce_zero(square - 49)`,
    // exactly as the substrate's `Op::Anchor` would: a constant wire, a
    // difference Lin, and a 1-term check.
    let pin = rec.add(|lc| lc.add_term(&Recorder::ONE, Coeff::Arbitrary(root_honest.square())));
    let diff = rec.add(|lc| lc.add(&square).add_term(&pin, Coeff::NegativeOne));
    rec.enforce_zero(|lc| lc.add(&diff)).unwrap();

    assert!(
        constraints_hold(&rec.events, &rec.values),
        "self-test honest circuit must satisfy its own constraints",
    );

    // Cheat the root; repair cannot reach `square` (no gate links them).
    let mut values = rec.values.clone();
    let delta = Fp::from(3u64);
    values[root] += delta;
    repair(&rec.events, &mut values, &[root]);
    let ragu_accepts = constraints_hold(&rec.events, &values);

    // True semantics: square must be root²; after the cheat it isn't 49.
    let native_ok = (root_honest + delta).square() == root_honest.square();

    assert_eq!(
        ragu_accepts, native_ok,
        "PATCHER SELF-TEST: the oracle failed to fire on a known \
         under-constrained alloc_square (ragu_accepts={ragu_accepts}, \
         native_ok={native_ok}). The soundness direction is vacuous — the \
         engine would miss real bugs.",
    );
}

fuzz_target!(|input: Input| {
    if std::env::var("PATCHER_SELFTEST").is_ok() {
        run_selftest();
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
    let mut rec = Recorder::new();
    let stacks = match synthesize(&mut rec, &mut (), &program, &honest_anchors) {
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

    // Resolve the coordinated cheat into (advice slot, delta) pairs,
    // deduplicated by slot so a wire is mutated at most once. A run with no
    // cheats is degenerate; default to a single cheat on the first advice
    // wire so every input does some work.
    let raw_cheats = if input.cheats.is_empty() {
        vec![Cheat {
            advice: 0,
            delta: 0,
        }]
    } else {
        input.cheats.clone()
    };
    let mut slot_delta: Vec<(usize, Fp)> = Vec::new();
    for ch in &raw_cheats {
        let slot = advice_slots[ch.advice as usize % advice_slots.len()];
        if slot_delta.iter().any(|(s, _)| *s == slot) {
            continue;
        }
        let mut delta = Fp::from(ch.delta);
        if delta == Fp::ZERO {
            delta = Fp::ONE;
        }
        slot_delta.push((slot, delta));
    }

    // ragu side: mutate every cheated advice wire, freeze them all, and
    // repair the rest through the captured constraints.
    let mut ragu_values = rec.values.clone();
    let frozen: Vec<usize> = slot_delta.iter().map(|(s, _)| slot_wires[*s]).collect();
    for (slot, delta) in &slot_delta {
        ragu_values[slot_wires[*slot]] += delta;
    }
    repair(&rec.events, &mut ragu_values, &frozen);
    let ragu_accepts = constraints_hold(&rec.events, &ragu_values);

    // native side: apply the same cheats and recompute the full chain.
    let overrides: Vec<(usize, Fp)> = slot_delta
        .iter()
        .map(|(slot, delta)| (*slot, shadow.elems[*slot] + delta))
        .collect();
    let native_ok = native_satisfied(
        &program,
        &honest_anchors,
        Overrides {
            elems: &overrides,
            ..Overrides::none()
        },
    );

    assert_eq!(
        ragu_accepts,
        native_ok,
        "PATCHER SOUNDNESS SIGNAL: cheating advice {slot_delta:?} \
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
