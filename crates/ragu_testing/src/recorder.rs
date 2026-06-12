//! The patcher engine: a recording driver plus a constraint-graph repair
//! solver (issues #728, #793, #796).
//!
//! [`Recorder`] is a [`Driver`] that captures the constraint graph ragu
//! actually emits during synthesis — every multiplication gate `a·b = c`,
//! every linear-combination wire, every `enforce_zero` — together with the
//! honest wire values, as a flat list of [`Event`]s over `usize` wires.
//!
//! [`repair`] then plays the malicious prover: given a witness whose free
//! advice wires have been mutated, it solves the captured constraints for
//! the remaining wires, propagating the cheat as far as the constraints
//! force it to go — and *no further*. A wire no constraint pins keeps its
//! honest value, and [`constraints_hold`] reports whether the result
//! satisfies every captured constraint. Comparing that verdict against an
//! independent native oracle is the patcher differential: ragu accepting a
//! witness the oracle rejects is an under-constrained-advice signal.
//!
//! The engine lives here rather than in the fuzz target so it is unit
//! tested ([`selftest`] runs in CI as a plain test) and reusable against
//! real circuits (issue #793).

use ff::{Field, PrimeField};
use ragu_arithmetic::Coeff;
use ragu_core::{
    Result,
    drivers::{Driver, DriverTypes, LinearExpression},
    gadgets::Bound,
    maybe::Always,
    routines::Routine,
};

/// A captured constraint / wire definition, in emission order.
#[derive(Clone, Debug)]
pub enum Event<F> {
    /// `out` is a virtual wire equal to `Σ coeff · wire` over `terms`.
    Lin {
        /// The virtual output wire.
        out: usize,
        /// The `(wire, coefficient)` terms of the combination.
        terms: Vec<(usize, F)>,
    },
    /// A multiplication gate: `values[a] · values[b] == values[c]`.
    Gate {
        /// The left input wire.
        a: usize,
        /// The right input wire.
        b: usize,
        /// The output wire.
        c: usize,
    },
    /// A constraint `Σ coeff · wire == 0` over `terms`.
    Enforce {
        /// The `(wire, coefficient)` terms of the constraint.
        terms: Vec<(usize, F)>,
    },
}

/// The recording driver. `Wire = usize`, an index into [`Recorder::values`].
pub struct Recorder<F> {
    /// The honest value of each wire, indexed by wire id.
    pub values: Vec<F>,
    /// The captured constraint graph, in emission order.
    pub events: Vec<Event<F>>,
}

impl<F: Field> Recorder<F> {
    /// The fixed wire holding the constant `1`.
    pub const ONE: usize = 0;

    /// An empty recorder whose only wire is the fixed ONE wire.
    pub fn new() -> Self {
        Recorder {
            values: vec![F::ONE],
            events: Vec::new(),
        }
    }

    /// Appends a raw wire with the given value and no defining constraint —
    /// free advice from the engine's perspective.
    pub fn push_wire(&mut self, value: F) -> usize {
        let id = self.values.len();
        self.values.push(value);
        id
    }
}

impl<F: Field> Default for Recorder<F> {
    fn default() -> Self {
        Self::new()
    }
}

/// Recording linear expression: accumulates `(wire, resolved_coeff)` terms,
/// folding the running gain into each coefficient as it is added. It records
/// only structure; the driver computes the resulting value from its own
/// wire table afterwards.
pub struct RecLc<F> {
    terms: Vec<(usize, F)>,
    gain: F,
}

impl<F: Field> Default for RecLc<F> {
    fn default() -> Self {
        RecLc {
            terms: Vec::new(),
            gain: F::ONE,
        }
    }
}

impl<F: Field> LinearExpression<usize, F> for RecLc<F> {
    fn add_term(mut self, wire: &usize, coeff: Coeff<F>) -> Self {
        let resolved = coeff.value() * self.gain;
        if resolved != F::ZERO {
            self.terms.push((*wire, resolved));
        }
        self
    }

    fn gain(mut self, coeff: Coeff<F>) -> Self {
        self.gain *= coeff.value();
        self
    }
}

impl<F: Field> DriverTypes for Recorder<F> {
    type ImplField = F;
    type ImplWire = usize;
    type MaybeKind = Always<()>;
    type LCadd = RecLc<F>;
    type LCenforce = RecLc<F>;
    type Extra = ();

    fn gate(
        &mut self,
        values: impl Fn() -> Result<(Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> Result<(usize, usize, usize, ())> {
        let (a, b, c) = values()?;
        let (a, b, c) = (a.value(), b.value(), c.value());
        let ia = self.push_wire(a);
        let ib = self.push_wire(b);
        let ic = self.push_wire(c);
        self.events.push(Event::Gate {
            a: ia,
            b: ib,
            c: ic,
        });
        Ok((ia, ib, ic, ()))
    }

    fn assign_extra(&mut self, _extra: (), value: impl Fn() -> Result<Coeff<F>>) -> Result<usize> {
        let v = value()?.value();
        Ok(self.push_wire(v))
    }
}

impl<'dr, F: Field> Driver<'dr> for Recorder<F> {
    type F = F;
    type Wire = usize;
    const ONE: usize = 0;

    fn add(&mut self, lc: impl Fn(RecLc<F>) -> RecLc<F>) -> usize {
        let built = lc(RecLc::default());
        let value = built.terms.iter().map(|(w, c)| self.values[*w] * c).sum();
        let out = self.push_wire(value);
        self.events.push(Event::Lin {
            out,
            terms: built.terms,
        });
        out
    }

    fn enforce_zero(&mut self, lc: impl Fn(RecLc<F>) -> RecLc<F>) -> Result<()> {
        let built = lc(RecLc::default());
        self.events.push(Event::Enforce { terms: built.terms });
        Ok(())
    }

    fn routine<R: Routine<F> + 'dr>(
        &mut self,
        _routine: R,
        _input: Bound<'dr, Self, R::Input>,
    ) -> Result<Bound<'dr, Self, R::Output>> {
        unreachable!("the recorder does not support routines yet (issue #793)")
    }
}

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
///   `c := a·b` (output), or an *input*, `a := c/b` or `b := c/a` (needed
///   for `invert`/`divide`, where the freshly-allocated inverse/quotient is
///   a gate input pinned by the surrounding copies). Input solves require
///   the known operand to be nonzero; otherwise the gate is left unsolved
///   and [`constraints_hold`] reports the resulting violation.
/// * `Enforce { terms }` — a linear constraint `Σ cᵢ·wᵢ = 0` with one
///   unknown term solves it (`wⱼ := −(Σ_{i≠j} cᵢ·wᵢ)/cⱼ`).
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
pub fn repair<F: Field>(events: &[Event<F>], values: &mut [F], free: &[usize]) {
    let mut known = vec![false; values.len()];
    known[Recorder::<F>::ONE] = true;
    for &w in free {
        known[w] = true;
    }

    loop {
        let mut changed = false;
        for ev in events {
            match ev {
                Event::Lin { out, terms } => {
                    if !known[*out] && terms.iter().all(|(w, _)| known[*w]) {
                        values[*out] = terms.iter().map(|(w, c)| values[*w] * c).sum();
                        known[*out] = true;
                        changed = true;
                    }
                }
                Event::Gate { a, b, c } => match (known[*a], known[*b], known[*c]) {
                    (true, true, false) => {
                        values[*c] = values[*a] * values[*b];
                        known[*c] = true;
                        changed = true;
                    }
                    (false, true, true) if values[*b] != F::ZERO => {
                        values[*a] = values[*c] * values[*b].invert().unwrap();
                        known[*a] = true;
                        changed = true;
                    }
                    (true, false, true) if values[*a] != F::ZERO => {
                        values[*b] = values[*c] * values[*a].invert().unwrap();
                        known[*b] = true;
                        changed = true;
                    }
                    _ => {}
                },
                Event::Enforce { terms } => {
                    let mut unknown = terms.iter().filter(|(w, _)| !known[*w]);
                    if let Some(&(uw, uc)) = unknown.next()
                        && unknown.next().is_none()
                        && uc != F::ZERO
                    {
                        // Σ cᵢ·wᵢ = 0, one unknown wⱼ ⇒ wⱼ = −(Σ_{i≠j} cᵢ·wᵢ)/cⱼ.
                        let rest: F = terms
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
pub fn constraints_hold<F: Field>(events: &[Event<F>], values: &[F]) -> bool {
    events.iter().all(|ev| match ev {
        Event::Lin { out, terms } => {
            values[*out] == terms.iter().map(|(w, c)| values[*w] * c).sum()
        }
        Event::Gate { a, b, c } => values[*a] * values[*b] == values[*c],
        Event::Enforce { terms } => terms.iter().map(|(w, c)| values[*w] * c).sum::<F>() == F::ZERO,
    })
}

/// Build a deliberately under-constrained circuit in the recorder and
/// assert the patcher's soundness signal fires. Panics if it does not.
///
/// The circuit allocates `root` and `square` as independent free wires and
/// anchors `square` to its honest value `root²`, but omits the
/// `square = root²` gate. Mutating `root` and repairing through the
/// captured constraints leaves `square` untouched (no rule carries the
/// change), so ragu accepts — while the true semantics say `square` must
/// move, violating the anchor. The mismatch is the signal.
///
/// This runs in CI as a unit test and on demand in the fuzz target
/// (`PATCHER_SELFTEST=1`): proof the soundness direction is not vacuous.
pub fn selftest<F: PrimeField>() {
    let root_honest = F::from(7u64);

    let mut rec = Recorder::<F>::new();
    let root = rec.push_wire(root_honest); // free advice
    let square = rec.push_wire(root_honest.square()); // free advice — BUG: not gated to root²

    // Anchor `square` to its honest value via `enforce_zero(square - 49)`,
    // exactly as the substrate's `Op::Anchor` would: a constant wire, a
    // difference Lin, and a 1-term check.
    let pin =
        rec.add(|lc| lc.add_term(&Recorder::<F>::ONE, Coeff::Arbitrary(root_honest.square())));
    let diff = rec.add(|lc| lc.add(&square).add_term(&pin, Coeff::NegativeOne));
    rec.enforce_zero(|lc| lc.add(&diff)).unwrap();

    assert!(
        constraints_hold(&rec.events, &rec.values),
        "self-test honest circuit must satisfy its own constraints",
    );

    // Cheat the root; repair cannot reach `square` (no gate links them).
    let mut values = rec.values.clone();
    let delta = F::from(3u64);
    values[root] += delta;
    repair(&rec.events, &mut values, &[root]);
    let ragu_accepts = constraints_hold(&rec.events, &values);

    // True semantics: square must be root²; after the cheat it isn't.
    let native_ok = (root_honest + delta).square() == root_honest.square();

    assert_ne!(
        ragu_accepts, native_ok,
        "PATCHER SELF-TEST: the oracle failed to fire on a known \
         under-constrained alloc_square (ragu_accepts={ragu_accepts}, \
         native_ok={native_ok}). The soundness direction is vacuous — the \
         engine would miss real bugs.",
    );
}

#[cfg(test)]
mod tests {
    use ragu_pasta::Fp;

    use super::*;

    /// The planted under-constrained circuit makes the oracle fire.
    #[test]
    fn selftest_fires() {
        selftest::<Fp>();
    }

    /// The complement of [`selftest`]: with the `square = root²` gate
    /// *present*, repair propagates the cheat into `square`, the anchor
    /// rejects, and the native oracle agrees — no signal.
    #[test]
    fn repair_propagates_through_gate() {
        let root_honest = Fp::from(7u64);

        let mut rec = Recorder::<Fp>::new();
        // alloc_square-style gate (root, root, square), with the two gate
        // inputs copy-constrained to each other.
        let (a, b, square, ()) = rec
            .gate(|| {
                Ok((
                    Coeff::Arbitrary(root_honest),
                    Coeff::Arbitrary(root_honest),
                    Coeff::Arbitrary(root_honest.square()),
                ))
            })
            .unwrap();
        rec.enforce_zero(|lc| lc.add(&a).add_term(&b, Coeff::NegativeOne))
            .unwrap();

        // Anchor `square` to its honest value.
        let pin =
            rec.add(|lc| lc.add_term(&Recorder::<Fp>::ONE, Coeff::Arbitrary(root_honest.square())));
        let diff = rec.add(|lc| lc.add(&square).add_term(&pin, Coeff::NegativeOne));
        rec.enforce_zero(|lc| lc.add(&diff)).unwrap();

        assert!(constraints_hold(&rec.events, &rec.values));

        // Cheat the root (gate input `a` is the free advice here); repair
        // carries it through the copy to `b`, the gate to `square`, and the
        // anchor catches it.
        let delta = Fp::from(3u64);
        let mut values = rec.values.clone();
        values[a] += delta;
        repair(&rec.events, &mut values, &[a]);

        let ragu_accepts = constraints_hold(&rec.events, &values);
        let native_ok = (root_honest + delta).square() == root_honest.square();
        assert_eq!(
            ragu_accepts, native_ok,
            "correctly constrained circuit must not produce a signal",
        );
        assert!(!ragu_accepts, "the anchor must reject the cheated witness");
    }
}
