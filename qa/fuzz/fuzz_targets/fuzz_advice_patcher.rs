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
//! `PATCHER_SELFTEST=1` builds a deliberately under-constrained circuit
//! directly in the recorder (a root and a "square" allocated as independent
//! free wires, with the `square = root²` gate omitted) and confirms the
//! oracle fires — proof the soundness direction is not vacuous.

#![no_main]

use arbitrary::Arbitrary;
use ff::{Field, PrimeField};
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
    AdviceSlot, Capabilities, Limits, OpKind, OpSet, Overrides, Program, native_satisfied,
    shadow_eval, special_value, synthesize,
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

/// Solve the captured constraint graph for the witness a malicious prover
/// could submit, given the free-advice wires it has chosen.
///
/// This is a monotone **single-unknown dataflow solver** (issue #796 item
/// 1). `free` seeds the *known* set with the prover's genuine degrees of
/// freedom (held at their — possibly mutated — values in `values`) plus the
/// fixed ONE wire; everything else is *derived*. The solver repeatedly
/// applies any constraint that has **exactly one** unknown wire, solving
/// for it:
///
/// * `Lin { out, terms }` — once every term is known, `out := Σ cᵢ·wᵢ`.
/// * `Gate { a, b, c }` — solve whichever single wire is unknown:
///   `c := a·b` (output), or — and this is what the old forward-only engine
///   could not do — an *input*, `a := c/b` or `b := c/a` (needed for
///   `invert`/`divide`, where the freshly-allocated inverse/quotient is a
///   gate input pinned by the surrounding copies). Input solves require the
///   known operand to be nonzero; otherwise the gate is left unsolved and
///   [`constraints_hold`] reports the resulting violation.
/// * `Enforce { terms }` — a linear constraint `Σ cᵢ·wᵢ = 0` with one
///   unknown term solves it (`wⱼ := −(Σ_{i≠j} cᵢ·wᵢ)/cⱼ`). This generalizes
///   the old 2-term copy rule to any arity.
///
/// # Why no false positives
///
/// The *known* set only grows, and a wire is solved only when it is the
/// **unique** unknown of some constraint — so each derived wire is pinned
/// by exactly one constraint and the order of application cannot matter
/// (constraint graphs are forward DAGs). There is no oscillation and no
/// chance of solving a genuine degree of freedom (those are seeded known
/// and never re-solved). A wire that no constraint can pin stays at its
/// honest value; any residual violation is caught by [`constraints_hold`].
fn repair(events: &[Ev], values: &mut [Fp], free: &[usize]) {
    let mut known = vec![false; values.len()];
    known[Recorder::ONE] = true;
    for &w in free {
        known[w] = true;
    }

    loop {
        let mut changed = false;
        for ev in events {
            match ev {
                Ev::Lin { out, terms } => {
                    if !known[*out] && terms.iter().all(|(w, _)| known[*w]) {
                        values[*out] = terms.iter().map(|(w, c)| values[*w] * c).sum();
                        known[*out] = true;
                        changed = true;
                    }
                }
                Ev::Gate { a, b, c } => match (known[*a], known[*b], known[*c]) {
                    (true, true, false) => {
                        values[*c] = values[*a] * values[*b];
                        known[*c] = true;
                        changed = true;
                    }
                    (false, true, true) if values[*b] != Fp::ZERO => {
                        values[*a] = values[*c] * values[*b].invert().unwrap();
                        known[*a] = true;
                        changed = true;
                    }
                    (true, false, true) if values[*a] != Fp::ZERO => {
                        values[*b] = values[*c] * values[*a].invert().unwrap();
                        known[*b] = true;
                        changed = true;
                    }
                    _ => {}
                },
                Ev::Enforce { terms } => {
                    let mut unknown = terms.iter().filter(|(w, _)| !known[*w]);
                    if let Some(&(uw, uc)) = unknown.next()
                        && unknown.next().is_none()
                        && uc != Fp::ZERO
                    {
                        // Σ cᵢ·wᵢ = 0, one unknown wⱼ ⇒ wⱼ = −(Σ_{i≠j} cᵢ·wᵢ)/cⱼ.
                        let rest: Fp = terms
                            .iter()
                            .filter(|(w, _)| *w != uw)
                            .map(|(w, c)| values[*w] * c)
                            .sum();
                        values[uw] = -rest * uc.invert().unwrap();
                        known[uw] = true;
                        changed = true;
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

    // ragu side: apply the cheats to the chosen advice wires, then solve the
    // captured constraint graph for the resulting witness. The *full*
    // free-advice set is held fixed (the prover's genuine degrees of
    // freedom — non-cheated advice stays honest); everything else is
    // re-derived by the single-unknown solver.
    let mut ragu_values = rec.values.clone();
    for (slot, value) in &slot_value {
        ragu_values[slot_wires[*slot]] = *value;
    }
    repair(&rec.events, &mut ragu_values, &stacks.advice_wires);
    let ragu_accepts = constraints_hold(&rec.events, &ragu_values);

    // native side: apply the same cheats and recompute the full chain.
    let mutated = shadow_eval::<Fp>(
        &program,
        Overrides {
            elems: &slot_value,
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
    if mutated.elems.len() != shadow.elems.len() || mutated.bools != shadow.bools {
        return;
    }
    let native_ok = mutated.anchors == honest_anchors;

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
