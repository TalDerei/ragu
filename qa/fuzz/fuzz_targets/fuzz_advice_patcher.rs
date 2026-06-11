//! The "patcher" technique with a real repair engine (issues #728, #793).
//!
//! `fuzz_circuit_cheat` is a patcher whose "repair" is re-running
//! `circuit.trace(mutated_witness)`: every wire — including advice — is
//! recomputed by the gadget's own witness logic. That can never expose an
//! under-constrained *advice* wire, because the gadget always recomputes
//! the *correct* advice on a re-run, masking a missing constraint.
//!
//! This target closes that gap. It runs the circuit through a **recording
//! driver** that captures the constraint graph ragu actually emits — every
//! multiplication gate `a·b=c`, every linear-combination wire, every
//! `enforce_zero` — together with the honest wire values. The patcher then
//! mutates one *free advice* wire and **repairs through the captured
//! constraints**, not through the gadget logic:
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
//! # The differential
//!
//! Alongside the captured graph the harness keeps a native `Fp` shadow
//! that knows each gadget's true semantics (the oracle), independent of
//! ragu. For the mutated witness:
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
//! Mutating a free advice wire that no anchor depends on leaves both
//! verdicts satisfied — correctly no signal, since unconstrained advice is
//! free to change.

#![no_main]

use arbitrary::Arbitrary;
use ff::Field;
use ff::PrimeField;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_arithmetic::Coeff;
use ragu_core::{
    Result as RaguResult,
    drivers::{Driver, DriverTypes, LinearExpression},
    maybe::{Always, Maybe},
    routines::Routine,
    gadgets::Bound,
};
use ragu_primitives::Element;

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
        self.events.push(Ev::Gate { a: ia, b: ib, c: ic });
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
        let value = built
            .terms
            .iter()
            .map(|(w, c)| self.values[*w] * c)
            .sum();
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
// Substrate: a fuzz-generated circuit over a stack of elements.
// ---------------------------------------------------------------------------

const NUM_INPUTS: usize = 4;

fn special_value(idx: u8) -> Fp {
    match idx % 8 {
        0 => Fp::ZERO,
        1 => Fp::ONE,
        2 => -Fp::ONE,
        3 => Fp::TWO_INV,
        4 => Fp::ROOT_OF_UNITY,
        5 => Fp::MULTIPLICATIVE_GENERATOR,
        6 => Fp::from(1u64 << 32),
        _ => Fp::from(u64::MAX),
    }
}

#[derive(Arbitrary, Debug, Clone, Copy)]
enum Op {
    Add(u8, u8),
    Sub(u8, u8),
    Mul(u8, u8),
    Scale(u8, u64),
    /// Allocate `(root, square)` where `root` is *free advice* whose honest
    /// value is `stack[a]`, and `square = root²` via `Element::alloc_square`.
    /// The root is the mutation target the patcher cares about.
    AllocSquare(u8),
    /// Pin `stack[a]` to its honest value via `enforce_zero(elem - const)`.
    Anchor(u8),
}

#[derive(Arbitrary, Debug)]
struct Input {
    seeds: [u64; NUM_INPUTS],
    special: [Option<u8>; NUM_INPUTS],
    ops: Vec<Op>,
    /// Which free advice wire to mutate (mod the advice count).
    cheat_advice: u16,
    cheat_delta: u64,
}

fn build_inputs(input: &Input) -> [Fp; NUM_INPUTS] {
    let mut out = [Fp::ZERO; NUM_INPUTS];
    for i in 0..NUM_INPUTS {
        out[i] = match input.special[i] {
            Some(idx) => special_value(idx),
            None => Fp::from(input.seeds[i]),
        };
    }
    out
}

/// Honest native shadow: every advice wire takes its honest value, derived
/// wires are computed from operands, and each `AllocSquare` root is seeded
/// from `stack[a]` (its only honest coupling to the rest of the circuit).
fn honest_stack(ops: &[Op], inputs: &[Fp; NUM_INPUTS]) -> Vec<Fp> {
    let mut stack: Vec<Fp> = inputs.to_vec();
    for op in ops {
        let len = stack.len();
        match *op {
            Op::Add(a, b) => stack.push(stack[a as usize % len] + stack[b as usize % len]),
            Op::Sub(a, b) => stack.push(stack[a as usize % len] - stack[b as usize % len]),
            Op::Mul(a, b) => stack.push(stack[a as usize % len] * stack[b as usize % len]),
            Op::Scale(a, c) => stack.push(stack[a as usize % len] * Fp::from(c)),
            Op::AllocSquare(a) => {
                let r = stack[a as usize % len];
                stack.push(r);
                stack.push(r.square());
            }
            Op::Anchor(_) => {}
        }
    }
    stack
}

/// Native shadow with cheats applied. Advice wires (inputs and `AllocSquare`
/// roots) are *independent* free wires: each takes its honest value unless
/// its own slot is overridden — cheating an upstream input does **not** move
/// a downstream root, mirroring ragu, where the root is decoupled advice.
/// Derived wires are recomputed from operands.
fn eval_with_advice(ops: &[Op], honest: &[Fp], overrides: &[(usize, Fp)]) -> Vec<Fp> {
    let ov = |slot: usize, base: Fp| -> Fp {
        overrides
            .iter()
            .find(|(s, _)| *s == slot)
            .map(|(_, v)| *v)
            .unwrap_or(base)
    };
    let mut stack: Vec<Fp> = (0..NUM_INPUTS).map(|i| ov(i, honest[i])).collect();
    for op in ops {
        let len = stack.len();
        match *op {
            Op::Add(a, b) => stack.push(stack[a as usize % len] + stack[b as usize % len]),
            Op::Sub(a, b) => stack.push(stack[a as usize % len] - stack[b as usize % len]),
            Op::Mul(a, b) => stack.push(stack[a as usize % len] * stack[b as usize % len]),
            Op::Scale(a, c) => stack.push(stack[a as usize % len] * Fp::from(c)),
            Op::AllocSquare(_) => {
                let root_slot = stack.len();
                let root = ov(root_slot, honest[root_slot]);
                stack.push(root);
                stack.push(root.square());
            }
            Op::Anchor(_) => {}
        }
    }
    stack
}

/// Returns the stack-slot indices that are *free advice*: the inputs and
/// every `AllocSquare` root. Stack growth is value-independent, so these
/// indices are identical for the native and recording runs.
fn advice_slots(ops: &[Op]) -> Vec<usize> {
    let mut slots: Vec<usize> = (0..NUM_INPUTS).collect();
    let mut len = NUM_INPUTS;
    for op in ops {
        match *op {
            Op::Add(..) | Op::Sub(..) | Op::Mul(..) | Op::Scale(..) => len += 1,
            Op::AllocSquare(_) => {
                slots.push(len); // root
                len += 2; // root, square
            }
            Op::Anchor(_) => {}
        }
    }
    slots
}

/// The stack slot each `Anchor` op pins, in encounter order. Stack growth
/// is value-independent, so these are stable across honest and cheat runs.
fn anchor_targets(ops: &[Op]) -> Vec<usize> {
    let mut len = NUM_INPUTS;
    let mut targets = Vec::new();
    for op in ops {
        match *op {
            Op::Anchor(a) => targets.push(a as usize % len),
            Op::Add(..) | Op::Sub(..) | Op::Mul(..) | Op::Scale(..) => len += 1,
            Op::AllocSquare(_) => len += 2,
        }
    }
    targets
}

/// Honest anchor values, in encounter order.
fn anchor_values(ops: &[Op], inputs: &[Fp; NUM_INPUTS]) -> Vec<Fp> {
    let stack = honest_stack(ops, inputs);
    anchor_targets(ops).iter().map(|s| stack[*s]).collect()
}

/// Native oracle verdict: with `overrides` applied, do all anchors still
/// equal their honest values?
fn native_satisfied(
    ops: &[Op],
    honest: &[Fp],
    honest_anchors: &[Fp],
    overrides: &[(usize, Fp)],
) -> bool {
    let stack = eval_with_advice(ops, honest, overrides);
    anchor_targets(ops)
        .iter()
        .zip(honest_anchors)
        .all(|(slot, want)| stack[*slot] == *want)
}

/// Synthesize the op stack through driver `D`, emitting the same anchors
/// (pinned to `honest_anchors`). Returns the per-slot wires so callers can
/// align advice slots with wire ids.
fn synthesize<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    ops: &[Op],
    inputs: &[Fp; NUM_INPUTS],
    honest_anchors: &[Fp],
    buggy: bool,
) -> RaguResult<Vec<D::Wire>> {
    let mut elems: Vec<Element<'dr, D>> = (0..NUM_INPUTS)
        .map(|i| {
            let v = inputs[i];
            Element::alloc(dr, &mut (), D::just(move || v))
        })
        .collect::<RaguResult<_>>()?;
    let mut anchor_idx = 0usize;
    for op in ops {
        let len = elems.len();
        match *op {
            Op::Add(a, b) => {
                let r = elems[a as usize % len].add(dr, &elems[b as usize % len]);
                elems.push(r);
            }
            Op::Sub(a, b) => {
                let r = elems[a as usize % len].sub(dr, &elems[b as usize % len]);
                elems.push(r);
            }
            Op::Mul(a, b) => {
                let r = elems[a as usize % len].mul(dr, &elems[b as usize % len])?;
                elems.push(r);
            }
            Op::Scale(a, c) => {
                let r = elems[a as usize % len].scale(dr, Coeff::Arbitrary(Fp::from(c)));
                elems.push(r);
            }
            Op::AllocSquare(a) => {
                let v = *elems[a as usize % len].value().take();
                if buggy {
                    // Self-test: a deliberately under-constrained `alloc_square`
                    // that allocates the root and its "square" as independent
                    // free wires, omitting the `square = root²` gate. The
                    // patcher must catch this when the square is anchored.
                    let sq = v.square();
                    let root = Element::alloc(dr, &mut (), D::just(move || v))?;
                    let square = Element::alloc(dr, &mut (), D::just(move || sq))?;
                    elems.push(root);
                    elems.push(square);
                } else {
                    let (root, square) = Element::alloc_square(dr, D::just(move || v))?;
                    elems.push(root);
                    elems.push(square);
                }
            }
            Op::Anchor(a) => {
                let slot = a as usize % len;
                let pin = Element::constant(dr, honest_anchors[anchor_idx]);
                anchor_idx += 1;
                elems[slot].sub(dr, &pin).enforce_zero(dr)?;
            }
        }
    }
    Ok(elems.iter().map(|e| e.wire().clone()).collect())
}

// ---------------------------------------------------------------------------
// Repair engine: propagate a mutation through the *captured* constraints.
// ---------------------------------------------------------------------------

/// Apply the captured constraint rules to `values` to a fixpoint:
/// * `Lin`  → recompute the virtual wire from its terms,
/// * `Gate` → force `c := a·b`,
/// * 2-term `Enforce` (`c1·w1 + c2·w2 == 0`) → force the *later* wire,
/// while never overwriting any wire in `frozen` (the mutation targets).
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
        Ev::Lin { out, terms } => {
            values[*out] == terms.iter().map(|(w, c)| values[*w] * c).sum()
        }
        Ev::Gate { a, b, c } => values[*a] * values[*b] == values[*c],
        Ev::Enforce { terms } => {
            terms.iter().map(|(w, c)| values[*w] * c).sum::<Fp>() == Fp::ZERO
        }
    })
}

fuzz_target!(|input: Input| {
    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!("{:#?}", input);
        return;
    }
    if input.ops.is_empty() || input.ops.len() > 48 {
        return;
    }

    let inputs = build_inputs(&input);
    let honest = honest_stack(&input.ops, &inputs);
    let honest_anchors = anchor_values(&input.ops, &inputs);
    let advice = advice_slots(&input.ops);
    if advice.is_empty() {
        return;
    }

    // PATCHER_SELFTEST=1 swaps in a deliberately under-constrained
    // `alloc_square` to confirm the oracle fires (the soundness direction).
    let buggy = std::env::var("PATCHER_SELFTEST").is_ok();

    // Record the honest constraint graph and the per-slot wire ids.
    let mut rec = Recorder::new();
    let slot_wires = match synthesize(&mut rec, &input.ops, &inputs, &honest_anchors, buggy) {
        Ok(w) => w,
        Err(_) => return,
    };

    // Completeness: the honest witness satisfies the captured constraints.
    assert!(
        constraints_hold(&rec.events, &rec.values),
        "honest witness violated a captured constraint (harness bug): {input:?}"
    );
    assert!(
        native_satisfied(&input.ops, &honest, &honest_anchors, &[]),
        "honest native oracle disagreed with itself (harness bug): {input:?}"
    );

    // Pick a free advice slot to cheat on, and its wire id.
    let cheat_slot = advice[input.cheat_advice as usize % advice.len()];
    let cheat_wire = slot_wires[cheat_slot];
    let mut delta = Fp::from(input.cheat_delta);
    if delta == Fp::ZERO {
        delta = Fp::ONE;
    }

    // ragu side: mutate the advice wire, repair through captured constraints.
    let mut ragu_values = rec.values.clone();
    ragu_values[cheat_wire] += delta;
    repair(&rec.events, &mut ragu_values, &[cheat_wire]);
    let ragu_accepts = constraints_hold(&rec.events, &ragu_values);

    // native side: mutate the same advice slot, recompute the full chain.
    let overrides = [(cheat_slot, honest[cheat_slot] + delta)];
    let native_ok = native_satisfied(&input.ops, &honest, &honest_anchors, &overrides);

    assert_eq!(
        ragu_accepts, native_ok,
        "PATCHER SOUNDNESS SIGNAL: cheating advice slot {cheat_slot} (wire {cheat_wire}) \
         by {delta:?} and repairing through the captured constraints, ragu {} the witness \
         but the native oracle says it is {}. {}. Input: {input:?}",
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
