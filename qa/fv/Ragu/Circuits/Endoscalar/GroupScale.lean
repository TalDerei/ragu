import Clean.Circuit
import Clean.Circuit.Loops
import Clean.Gadgets.Boolean
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Point.AddIncompleteUnchecked
import Ragu.Circuits.Point.ConditionalEndo
import Ragu.Circuits.Point.ConditionalNegate
import Ragu.Circuits.Point.Double
import Ragu.Circuits.Point.DoubleAndAddIncompleteUnchecked
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Endoscalar.GroupScale
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : F p)]

/-- `Endoscalar::group_scale(p)` scales a curve point `p` by the 128-bit
endoscalar's bits. Implements Algorithm 1 from BGH19 (the Halo paper). Mirrors
`crates/ragu_primitives/src/endoscalar.rs::Endoscalar::group_scale`.

Init: `acc₀ = (p.endo() + p).double()` — i.e., `acc₀ = [2]·(ζ·p + p)`.
Loop (64 iters): each iteration is one `Step.circuit` subcircuit taking a
2-bit pair `(n, e)`, building `s = (e=1 ? ζ·p.x : p.x, n=1 ? -p.y : p.y)`,
then updating `acc' = [2]·acc + s` via `double_and_add_incomplete`.

Bundling the iteration into a single `Step` subcircuit keeps the
`Circuit.foldlRange` body a one-subcircuit call, so the `circuit_norm`-tagged
`foldlRange` lemmas collapse the loop into a per-iteration `Step.Spec` chain
within the default heartbeat budget (the same reason `NonzeroBank.Scope`
needs no `set_option`s).

Non-degeneracy: the deployed gadget creates its `NonzeroBank` with
`NonzeroBank::new_unchecked()`, so **no** fold or discharge constraints are
emitted — every `add_incomplete` / `double_and_add_incomplete` distinct-x
condition rests on the Appendix C no-collision argument of BGH19 (see the
soundness comment in `Endoscalar::group_scale`), not on the constraint
system. This reimpl models exactly that via the `*Unchecked` point
sub-gadgets, and carries the non-degeneracy as the explicit caller
obligation `groupScaleNative ≠ none` in `Assumptions` — soundness is
*conditional* on it, which is the honest statement about the circuit that
ships. The extraction instance mirrors the unchecked bank.

The accumulator is chained symbolically, exactly as the deployed gadget
does: each `Step` returns its unchecked DAA's output expressions, and the
loop is a `Circuit.foldlRange` (the body's output depends on the accumulator,
so `Circuit.foldl`'s `ConstantOutput` does not apply). The fingerprint hashes
polynomial normal forms, so the tree shape of those expressions is
irrelevant to equivalence; `DoubleAndAddIncompleteUnchecked` spells `x_s` in
its cancelled form only so the symbolic term stays linear in the iteration
count on the Lean side. -/
structure Input (F : Type) where
  bits : Vector F 128
  pt : Point.Spec.Point F
deriving ProvableStruct

/-- One native step: given current acc and (n, e), compute `acc' = 2·acc + s`
where `s = (e=1 ? ζ·p.x : p.x, n=1 ? -p.y : p.y)`. Returns `none` if either
intermediate `add_incomplete` fails. -/
def stepNative (curveParams : Point.Spec.CurveParams p)
    (pt acc : Point.Spec.Point (F p)) (n e : F p) : Option (Point.Spec.Point (F p)) :=
  let s : Point.Spec.Point (F p) :=
    ⟨if e = 1 then curveParams.ζ * pt.x else pt.x,
     if n = 1 then -pt.y else pt.y⟩
  match acc.add_incomplete s with
  | none => none
  | some r => r.add_incomplete acc

/-- Initial accumulator: `(p.endo + p).double`. -/
def initAcc (curveParams : Point.Spec.CurveParams p) (pt : Point.Spec.Point (F p))
    : Option (Point.Spec.Point (F p)) :=
  match (pt.endo curveParams).add_incomplete pt with
  | none => none
  | some pre => pre.double

/-- Accumulator after `m` iterations of the loop, starting from `initAcc`. -/
def accAfter (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128) : ℕ → Option (Point.Spec.Point (F p))
  | 0 => initAcc curveParams pt
  | m + 1 =>
    match accAfter curveParams pt bits m with
    | none => none
    | some acc =>
      if h : 2 * m + 1 < 128 then
        stepNative curveParams pt acc
          (bits[2 * m]'(by omega)) (bits[2 * m + 1]'h)
      else
        none

/-- Native group-scaling result: `acc₆₄`. -/
def groupScaleNative (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128) : Option (Point.Spec.Point (F p)) :=
  accAfter curveParams pt bits 64

/-! ## One loop iteration, bundled as its own subcircuit.

A sub-gadget in the fv-review sense: used only as a subcircuit of
`GroupScale.main`, so it gets a Lean reimpl + proofs but no extraction
instance / autogen / formal instance of its own. Its correctness reaches the
top via composition — `GroupScale.soundness` consumes `Step.Spec` through the
`foldlRange`'s `circuit_norm` lemmas. -/
namespace Step

/-- One iteration's inputs: the 2-bit pair `(n, e)`, the base point `pt`,
and the running accumulator `acc`. No hint input: the unchecked DAA emits no
discharge, so there is no inverse to witness. -/
structure Input (F : Type) where
  n : F
  e : F
  pt : Point.Spec.Point F
  acc : Point.Spec.Point F
deriving ProvableStruct

/-- ConditionalNegate + ConditionalEndo build `s` from `(n, e)` and `pt`;
the unchecked DoubleAndAddIncomplete computes `2·acc + s`, and its output
expressions are returned as-is — the deployed gadget chains them the same
way. -/
def main (curveParams : Point.Spec.CurveParams p) (input : Var Input (F p))
    : Circuit (F p) (Var Point.Spec.Point (F p)) := do
  let s_neg ← Point.ConditionalNegate.circuit ⟨input.n, input.pt.x, input.pt.y⟩
  let s ← Point.ConditionalEndo.circuit curveParams ⟨input.e, s_neg.x, s_neg.y⟩
  Point.DoubleAndAddIncompleteUnchecked.circuit curveParams ⟨input.acc, s⟩

/-- Caller obligations, shared by soundness and completeness: curve
membership, boolean bits, and the step's non-degeneracy — the unchecked DAA
does not enforce its distinct-x conditions, so they enter as the assumption
`stepNative ≠ none` (justified at the `GroupScale` level by Appendix C of
BGH19, via `groupScaleNative ≠ none`). -/
def Assumptions (curveParams : Point.Spec.CurveParams p) (input : Input (F p)) :=
  input.pt.isOnCurve curveParams ∧
  input.acc.isOnCurve curveParams ∧
  IsBool input.n ∧
  IsBool input.e ∧
  stepNative curveParams input.pt input.acc input.n input.e ≠ none

def Spec (curveParams : Point.Spec.CurveParams p)
    (input : Input (F p)) (output : Point.Spec.Point (F p)) :=
  stepNative curveParams input.pt input.acc input.n input.e = some output ∧
  output.isOnCurve curveParams

instance elaborated (curveParams : Point.Spec.CurveParams p)
    : ElaboratedCircuit (F p) Input Point.Spec.Point (main curveParams) where
  -- CondNegate (3) + CondEndo (3) + unchecked DAA (15) = 21
  localLength _ := 21
  -- The DAA's output on the layout: `s = (pt.x + endo-select wire, pt.y +
  -- negate-select wire)`, then the DAA's two Square product wires and its
  -- trailing Mul product wire. Explicit so `GroupScale`'s proofs get a
  -- shallow projection instead of a whnf through the three sub-gadgets.
  output input offset :=
    ⟨varFromOffset field (offset + 3 + 3 + 3 + 3 + 3 + 2) -
        varFromOffset field (offset + 3 + 3 + 3 + 2) +
        (input.pt.x + varFromOffset field (offset + 3 + 2)),
     varFromOffset field (offset + 3 + 3 + 3 + 3 + 3 + 3 + 2) - input.acc.y⟩
  localLength_eq := by
    simp +arith [main, circuit_norm,
      Point.ConditionalNegate.circuit, Point.ConditionalEndo.circuit,
      Point.DoubleAndAddIncompleteUnchecked.circuit]
  output_eq := by
    intro input offset
    simp +arith [main, circuit_norm,
      Point.ConditionalNegate.circuit, Point.ConditionalEndo.circuit,
      Point.DoubleAndAddIncompleteUnchecked.circuit]
  subcircuitsConsistent := by
    simp +arith [main, circuit_norm,
      Point.ConditionalNegate.circuit, Point.ConditionalEndo.circuit,
      Point.DoubleAndAddIncompleteUnchecked.circuit]

omit [NeZero (2 : F p)] in
theorem soundness (curveParams : Point.Spec.CurveParams p) :
    Soundness (F p) (Input := Input) (Output := Point.Spec.Point) (main curveParams)
      (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start [Point.ConditionalNegate.circuit, Point.ConditionalNegate.Assumptions,
    Point.ConditionalNegate.Spec,
    Point.ConditionalEndo.circuit, Point.ConditionalEndo.Assumptions,
    Point.ConditionalEndo.Spec,
    Point.DoubleAndAddIncompleteUnchecked.circuit,
    Point.DoubleAndAddIncompleteUnchecked.Assumptions,
    Point.DoubleAndAddIncompleteUnchecked.Spec]
  obtain ⟨h_pt_curve, h_acc_curve, h_n_bool, h_e_bool, h_step_ne⟩ := h_assumptions
  obtain ⟨h_neg, h_endo, h_daa⟩ := h_holds
  have h_sy := h_neg h_n_bool
  have h_sx := h_endo h_e_bool
  -- Split the native-step assumption into the two-addition chain, in terms of
  -- the s wires.
  simp only [stepNative] at h_step_ne
  rw [← h_sx, ← h_sy] at h_step_ne
  have h_add1_ne : (⟨input_acc_x, input_acc_y⟩ : Point.Spec.Point (F p)).add_incomplete
      ⟨input_pt_x + env.get (i₀ + 3 + 2), input_pt_y + env.get (i₀ + 2)⟩ ≠ none := by
    intro h
    rw [h] at h_step_ne
    exact h_step_ne rfl
  obtain ⟨r0, h_add1⟩ := Option.ne_none_iff_exists'.mp h_add1_ne
  rw [h_add1] at h_step_ne
  obtain ⟨out0, h_add2⟩ := Option.ne_none_iff_exists'.mp h_step_ne
  -- s is on the curve: y² is invariant under negation, x³ under ζ-scaling.
  have h_s_curve : (⟨input_pt_x + env.get (i₀ + 3 + 2),
      input_pt_y + env.get (i₀ + 2)⟩ : Point.Spec.Point (F p)).isOnCurve curveParams := by
    simp only [Point.Spec.Point.isOnCurve] at h_pt_curve ⊢
    rw [h_sx, h_sy]
    rcases h_n_bool with hn | hn <;> rcases h_e_bool with he | he <;>
      simp only [hn, he, zero_ne_one, if_false, if_true, neg_sq, mul_pow,
        curveParams.h_small_order, one_mul] <;>
      exact h_pt_curve
  obtain ⟨r, h_add1', h_add2', h_out_curve⟩ :=
    h_daa ⟨h_acc_curve, h_s_curve, r0, out0, h_add1, h_add2⟩
  refine ⟨?_, h_out_curve⟩
  simp only [stepNative]
  rw [← h_sx, ← h_sy, h_add1']
  exact h_add2'

omit [NeZero (2 : F p)] in
theorem completeness (curveParams : Point.Spec.CurveParams p) :
    Completeness (F p) (Input := Input) (Output := Point.Spec.Point) (main curveParams) (Assumptions curveParams) := by
  circuit_proof_start [Point.ConditionalNegate.circuit, Point.ConditionalNegate.Assumptions,
    Point.ConditionalNegate.Spec,
    Point.ConditionalEndo.circuit, Point.ConditionalEndo.Assumptions,
    Point.ConditionalEndo.Spec,
    Point.DoubleAndAddIncompleteUnchecked.circuit,
    Point.DoubleAndAddIncompleteUnchecked.Assumptions,
    Point.DoubleAndAddIncompleteUnchecked.Spec]
  obtain ⟨h_pt_curve, h_acc_curve, h_n_bool, h_e_bool, h_step_ne⟩ := h_assumptions
  obtain ⟨h_neg_env, h_endo_env, _⟩ := h_env
  have h_sy := h_neg_env h_n_bool
  have h_sx := h_endo_env h_e_bool
  -- Split the native-step assumption into the two-addition chain, in terms of
  -- the s wires.
  simp only [stepNative] at h_step_ne
  rw [← h_sx, ← h_sy] at h_step_ne
  have h_add1_ne : (⟨input_acc_x, input_acc_y⟩ : Point.Spec.Point (F p)).add_incomplete
      ⟨input_pt_x + env.get (i₀ + 3 + 2), input_pt_y + env.get (i₀ + 2)⟩ ≠ none := by
    intro h
    rw [h] at h_step_ne
    exact h_step_ne rfl
  obtain ⟨r0, h_add1⟩ := Option.ne_none_iff_exists'.mp h_add1_ne
  rw [h_add1] at h_step_ne
  obtain ⟨out0, h_add2⟩ := Option.ne_none_iff_exists'.mp h_step_ne
  -- s is on the curve: y² is invariant under negation, x³ under ζ-scaling.
  have h_s_curve : (⟨input_pt_x + env.get (i₀ + 3 + 2),
      input_pt_y + env.get (i₀ + 2)⟩ : Point.Spec.Point (F p)).isOnCurve curveParams := by
    simp only [Point.Spec.Point.isOnCurve] at h_pt_curve ⊢
    rw [h_sx, h_sy]
    rcases h_n_bool with hn | hn <;> rcases h_e_bool with he | he <;>
      simp only [hn, he, zero_ne_one, if_false, if_true, neg_sq, mul_pow,
        curveParams.h_small_order, one_mul] <;>
      exact h_pt_curve
  exact ⟨h_n_bool, h_e_bool, h_acc_curve, h_s_curve, r0, out0, h_add1, h_add2⟩

def circuit (curveParams : Point.Spec.CurveParams p) :
    FormalCircuit (F p) Input Point.Spec.Point :=
  { main := main curveParams,
    elaborated := elaborated curveParams,
    Assumptions := Assumptions curveParams
    Spec := Spec curveParams
    soundness := soundness curveParams
    completeness := completeness curveParams }

end Step

/-- `Circuit.foldlRange` needs an inhabited accumulator type; file-local so
it leaks into no importer. -/
local instance : Inhabited (Var Point.Spec.Point (F p)) := ⟨⟨0, 0⟩⟩

/-- `@[irreducible]` is a defeq seal only: it stops the unifier/kernel from
whnf-unrolling the 64-iteration foldl during structure-update type checks
(e.g. the `circuit` bundle below), which exceeds the default heartbeat
budget. Proofs still unfold `main` fine via its equation lemma
(`simp [main, ...]`). -/
@[irreducible]
def main (curveParams : Point.Spec.CurveParams p) (input : Var Input (F p))
    : Circuit (F p) (Var Point.Spec.Point (F p)) := do
  -- p_endo = (ζ·p.x, p.y) — pure scale, no constraints.
  let p_endo : Var Point.Spec.Point (F p) := ⟨curveParams.ζ * input.pt.x, input.pt.y⟩
  -- acc_pre = p_endo + p; the unchecked AddIncomplete emits no bank
  -- constraints, mirroring the deployed gadget's `new_unchecked()` bank.
  let acc_pre ← Point.AddIncompleteUnchecked.circuit curveParams ⟨p_endo, input.pt⟩
  -- acc₀ = acc_pre.double()
  let acc_0 ← Point.Double.circuit curveParams acc_pre
  -- 64 iterations, each a single `Step.circuit` subcircuit. `foldlRange`
  -- rather than `foldl`: the body's output is the DAA's symbolic output, which
  -- depends on the accumulator, so `ConstantOutput` does not hold.
  Circuit.foldlRange 64 acc_0
    (fun acc i =>
      Step.circuit curveParams
        ⟨input.bits[2 * i.val]'(by have := i.isLt; omega),
         input.bits[2 * i.val + 1]'(by have := i.isLt; omega),
         input.pt, acc⟩)
    -- `Step.circuit`'s `localLength` is the constant 21; the autoparam's
    -- `simp only [circuit_norm]` cannot see through the bundle.
    (by
      apply Circuit.ConstantLength.fromConstantLength'
      intros
      simp only [circuit_norm, Step.circuit, Step.elaborated])

/-- Caller obligations. `groupScaleNative ≠ none` is the Appendix C
no-collision condition: the unchecked additions emit no distinct-x
constraints, so soundness is conditional on it. For transcript-derived
endoscalars on the Pasta curves this holds by the BGH19 Appendix C bound
(whose integer core is formalized in `Ragu.Lemmas.EndoscalarProof`). The
remaining curve-side bridge from that core to this affine `groupScaleNative`
precondition is still future work, so the condition remains an assumption here. -/
def Assumptions (curveParams : Point.Spec.CurveParams p) (input : Input (F p)) :=
  input.pt.isOnCurve curveParams ∧
  curveParams.noOrderTwoPoints ∧
  (∀ i : Fin 128, IsBool input.bits[i]) ∧
  groupScaleNative curveParams input.pt input.bits ≠ none

def Spec (curveParams : Point.Spec.CurveParams p) (input : Input (F p))
    (output : Point.Spec.Point (F p)) :=
  groupScaleNative curveParams input.pt input.bits = some output ∧
  output.isOnCurve curveParams

instance elaborated (curveParams : Point.Spec.CurveParams p)
    : ElaboratedCircuit (F p) Input Point.Spec.Point (main curveParams) where
  -- 9 (unchecked AddIncomplete) + 12 (Double) + 64 × 21 (Step) = 1365
  localLength _ := 9 + 12 + 64 * 21
  localLength_eq := by
    simp +arith [main, circuit_norm,
      Point.AddIncompleteUnchecked.circuit, Point.Double.circuit, Step.circuit,
      Step.elaborated]
  subcircuitsConsistent := by
    simp +arith [main, circuit_norm,
      Point.AddIncompleteUnchecked.circuit, Point.Double.circuit, Step.circuit,
      Step.elaborated]
  channelsLawful := by
    simp +arith [main, circuit_norm,
      Point.AddIncompleteUnchecked.circuit, Point.Double.circuit, Step.circuit,
      Step.elaborated]

/-! ## Native helpers for threading the non-degeneracy chain.

Both soundness and completeness use these helpers to extract each unchecked
addition's distinct-x precondition from the single top-level
`groupScaleNative ≠ none` premise. The unchecked point gadgets do not emit
constraints for those preconditions; they consume them through `Assumptions`. -/

-- `accAfter` is `none` from m onward, once it's `none` at some step ≤ m.
-- (Line comments: `omit` doesn't bind through `/-- -/` docstrings.)
omit [NeZero (2 : F p)] in
private lemma accAfter_none_persists (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128) :
    ∀ k m, k ≤ m → accAfter curveParams pt bits k = none →
      accAfter curveParams pt bits m = none := by
  intro k m hkm h_none
  induction m with
  | zero =>
    interval_cases k; exact h_none
  | succ m ih =>
    by_cases hkm' : k ≤ m
    · simp only [accAfter, ih hkm']
    · have : k = m + 1 := by omega
      rw [this] at h_none; exact h_none

-- If `accAfter ... (m+1) ≠ none`, then `accAfter ... m ≠ none`.
omit [NeZero (2 : F p)] in
private lemma accAfter_ne_succ_imp (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128) (m : ℕ)
    (h : accAfter curveParams pt bits (m + 1) ≠ none) :
    accAfter curveParams pt bits m ≠ none := by
  intro hm
  apply h
  simp only [accAfter, hm]

-- If `groupScaleNative ≠ none`, every `accAfter m` for `m ≤ 64` is `≠ none`.
omit [NeZero (2 : F p)] in
private lemma all_accAfter_ne (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128)
    (h : groupScaleNative curveParams pt bits ≠ none) :
    ∀ m ≤ 64, accAfter curveParams pt bits m ≠ none := by
  intro m hm hm_none
  apply h
  exact accAfter_none_persists curveParams pt bits m 64 hm hm_none

-- One-step unfolding of `accAfter` at a known `some` accumulator. Avoids
-- `simp only [accAfter]` in the inductive proofs, which would recursively
-- unfold the scrutinee all the way down to `initAcc`.
omit [NeZero (2 : F p)] in
private lemma accAfter_succ_of_some (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128) (m : ℕ)
    (prev : Point.Spec.Point (F p))
    (h : accAfter curveParams pt bits m = some prev) (hm : 2 * m + 1 < 128) :
    accAfter curveParams pt bits (m + 1) =
      stepNative curveParams pt prev (bits[2 * m]'(by omega)) (bits[2 * m + 1]'hm) := by
  simp only [accAfter, h]
  rw [dif_pos hm]

/-! ## The symbolic accumulator of the `foldlRange`.

`Circuit.foldlRange` has no `ConstantOutput`, so its `circuit_norm` lemmas
leave the accumulator entering iteration `i` as Clean's
`Circuit.FoldlM.foldlAcc … i`: a `Fin.foldl` of the body's symbolic outputs.
The lemmas below peel that fold one iteration at a time and thread the
per-iteration `Step` facts through the native `accAfter` recursion. They are
stated for an arbitrary fold body: the body, the initial accumulator and the
wire offset are recovered by unification when the lemmas are applied to the
`circuit_proof_start` hypotheses, so the proofs never spell out the
`subcircuit` term Clean builds for `Step.circuit`. -/

omit [NeZero (2 : F p)] in
/-- The symbolic accumulator entering iteration `i` of a 64-iteration fold
with body `body`, starting from `init` at wire offset `n`. -/
private abbrev accVar (n : ℕ)
    (body : Var Point.Spec.Point (F p) → Fin 64 → Circuit (F p) (Var Point.Spec.Point (F p)))
    (init : Var Point.Spec.Point (F p)) (i : Fin 64) : Var Point.Spec.Point (F p) :=
  Circuit.FoldlM.foldlAcc n (Vector.finRange 64) body init i

omit [NeZero (2 : F p)] in
/-- Evaluate a symbolic point. -/
private abbrev evalPt (env : Environment (F p)) (v : Var Point.Spec.Point (F p)) :
    Point.Spec.Point (F p) :=
  ⟨Expression.eval env v.x, Expression.eval env v.y⟩

omit [NeZero (2 : F p)] in
/-- A `Step`'s output at wire offset `off`, in the shape `circuit_proof_start`
evaluates it to: the unchecked DAA's `x_s` wires (`lambda_2_sq - lambda_1_sq +
(pt.x + endo-select wire)`), and its `y_s` wire minus the accumulator's `y`,
which stays symbolic. -/
private abbrev stepOut (env : Environment (F p)) (pt_x acc_y : F p) (off : ℕ) :
    Point.Spec.Point (F p) :=
  ⟨env.get (off + 3 + 3 + 3 + 3 + 3 + 2) - env.get (off + 3 + 3 + 3 + 2) +
      (pt_x + env.get (off + 3 + 2)),
   env.get (off + 3 + 3 + 3 + 3 + 3 + 3 + 2) - acc_y⟩

omit [NeZero (2 : F p)] in
-- Iteration `i + 1`'s accumulator is the body's output on iteration `i`'s.
private lemma accVar_succ (n : ℕ)
    (body : Var Point.Spec.Point (F p) → Fin 64 → Circuit (F p) (Var Point.Spec.Point (F p)))
    (init : Var Point.Spec.Point (F p)) (hlen : ∀ acc i, (body acc i).localLength = 21)
    (i : ℕ) (hi : i + 1 < 64) :
    accVar n body init ⟨i + 1, hi⟩ =
      (body (accVar n body init ⟨i, by omega⟩) ⟨i, by omega⟩).output (n + i * 21) := by
  simp only [accVar, Circuit.FoldlM.foldlAcc, Fin.val_mk]
  rw [Fin.foldl_succ_last]
  simp only [Vector.getElem_finRange, Fin.val_castSucc, Fin.val_last, hlen]

omit [NeZero (2 : F p)] in
-- The fold's final output is the body's output on the last accumulator.
private lemma fin_foldl_eq_last (n : ℕ)
    (body : Var Point.Spec.Point (F p) → Fin 64 → Circuit (F p) (Var Point.Spec.Point (F p)))
    (init : Var Point.Spec.Point (F p)) (hlen : ∀ acc i, (body acc i).localLength = 21) :
    Fin.foldl 64 (fun acc i => (body acc i).output (n + i.val * 21)) init =
      (body (accVar n body init ⟨63, by omega⟩) ⟨63, by omega⟩).output
        (n + (⟨63, by omega⟩ : Fin 64).val * 21) := by
  rw [Fin.foldl_succ_last]
  simp only [accVar, Circuit.FoldlM.foldlAcc, Vector.getElem_finRange, Fin.last, Fin.val_mk,
    Fin.castSucc, Fin.castAdd, Fin.castLE, hlen]

omit [NeZero (2 : F p)] in
-- Threading the per-iteration `Step` facts through `accAfter`: for every
-- `m < 64`, the symbolic accumulator entering iteration `m` evaluates to
-- `accAfter m`, which is `some` and on the curve. `h_steps` is the fold's
-- `circuit_norm` residue (one `Step.Assumptions → Step.Spec` per iteration),
-- `h_link` the evaluation of the body's output, `h0` the init chain.
private lemma fold_inv (curveParams : Point.Spec.CurveParams p) (env : Environment (F p))
    (bits : Vector (F p) 128) (bits_var : Vector (Expression (F p)) 128)
    (pt : Point.Spec.Point (F p))
    (body : Var Point.Spec.Point (F p) → Fin 64 → Circuit (F p) (Var Point.Spec.Point (F p)))
    (init : Var Point.Spec.Point (F p)) (n : ℕ)
    (h_bit : ∀ (j : ℕ) (hj : j < 128), Expression.eval env (bits_var[j]'hj) = bits[j]'hj)
    (h_pt : pt.isOnCurve curveParams)
    (h_bool : ∀ i : Fin 128, IsBool bits[i])
    (h_ne : groupScaleNative curveParams pt bits ≠ none)
    (h_steps : ∀ i : Fin 64,
      Step.Assumptions curveParams
        ⟨Expression.eval env (bits_var[2 * i.val]'(by have := i.isLt; omega)),
         Expression.eval env (bits_var[2 * i.val + 1]'(by have := i.isLt; omega)),
         pt, evalPt env (accVar n body init i)⟩ →
      Step.Spec curveParams
        ⟨Expression.eval env (bits_var[2 * i.val]'(by have := i.isLt; omega)),
         Expression.eval env (bits_var[2 * i.val + 1]'(by have := i.isLt; omega)),
         pt, evalPt env (accVar n body init i)⟩
        (stepOut env pt.x (Expression.eval env (accVar n body init i).y) (n + i.val * 21)))
    (hlen : ∀ acc i, (body acc i).localLength = 21)
    (h_link : ∀ acc (i : Fin 64),
      evalPt env ((body acc i).output (n + i.val * 21)) =
        stepOut env pt.x (Expression.eval env acc.y) (n + i.val * 21))
    (h0 : accAfter curveParams pt bits 0 = some (evalPt env init) ∧
      (evalPt env init).isOnCurve curveParams) :
    ∀ (m : ℕ) (hm : m < 64),
      accAfter curveParams pt bits m = some (evalPt env (accVar n body init ⟨m, hm⟩)) ∧
      (evalPt env (accVar n body init ⟨m, hm⟩)).isOnCurve curveParams := by
  intro m
  induction m with
  | zero =>
    intro hm
    simpa only [accVar, Circuit.FoldlM.foldlAcc, Fin.val_mk, Fin.foldl_zero] using h0
  | succ k ih =>
    intro hm
    have hk : k < 64 := by omega
    obtain ⟨h_prev, h_prev_curve⟩ := ih hk
    have h_acck := accAfter_succ_of_some curveParams pt bits k _ h_prev (by omega)
    have h_nek := all_accAfter_ne curveParams pt bits h_ne (k + 1) (by omega)
    rw [h_acck] at h_nek
    have h := h_steps ⟨k, hk⟩
    simp only [Step.Assumptions, Step.Spec, h_bit] at h
    obtain ⟨h_s, h_c⟩ := h ⟨h_pt, h_prev_curve, h_bool ⟨2 * k, by omega⟩,
      h_bool ⟨2 * k + 1, by omega⟩, h_nek⟩
    rw [accVar_succ n body init hlen k hm, h_link, h_acck]
    exact ⟨h_s, h_c⟩

omit [NeZero (2 : F p)] in
-- The fold's final output evaluates to `groupScaleNative` and lies on the
-- curve.
private lemma fold_final (curveParams : Point.Spec.CurveParams p) (env : Environment (F p))
    (bits : Vector (F p) 128) (bits_var : Vector (Expression (F p)) 128)
    (pt : Point.Spec.Point (F p))
    (body : Var Point.Spec.Point (F p) → Fin 64 → Circuit (F p) (Var Point.Spec.Point (F p)))
    (init : Var Point.Spec.Point (F p)) (n : ℕ)
    (h_bit : ∀ (j : ℕ) (hj : j < 128), Expression.eval env (bits_var[j]'hj) = bits[j]'hj)
    (h_pt : pt.isOnCurve curveParams)
    (h_bool : ∀ i : Fin 128, IsBool bits[i])
    (h_ne : groupScaleNative curveParams pt bits ≠ none)
    (h_steps : ∀ i : Fin 64,
      Step.Assumptions curveParams
        ⟨Expression.eval env (bits_var[2 * i.val]'(by have := i.isLt; omega)),
         Expression.eval env (bits_var[2 * i.val + 1]'(by have := i.isLt; omega)),
         pt, evalPt env (accVar n body init i)⟩ →
      Step.Spec curveParams
        ⟨Expression.eval env (bits_var[2 * i.val]'(by have := i.isLt; omega)),
         Expression.eval env (bits_var[2 * i.val + 1]'(by have := i.isLt; omega)),
         pt, evalPt env (accVar n body init i)⟩
        (stepOut env pt.x (Expression.eval env (accVar n body init i).y) (n + i.val * 21)))
    (hlen : ∀ acc i, (body acc i).localLength = 21)
    (h_link : ∀ acc (i : Fin 64),
      evalPt env ((body acc i).output (n + i.val * 21)) =
        stepOut env pt.x (Expression.eval env acc.y) (n + i.val * 21))
    (h0 : accAfter curveParams pt bits 0 = some (evalPt env init) ∧
      (evalPt env init).isOnCurve curveParams) :
    groupScaleNative curveParams pt bits =
      some (evalPt env (Fin.foldl 64 (fun acc i => (body acc i).output (n + i.val * 21)) init)) ∧
    (evalPt env (Fin.foldl 64 (fun acc i => (body acc i).output (n + i.val * 21)) init)).isOnCurve
      curveParams := by
  obtain ⟨h63, h63_curve⟩ :=
    fold_inv curveParams env bits bits_var pt body init n h_bit h_pt h_bool h_ne h_steps hlen
      h_link h0 63 (by omega)
  have h_acc64 : accAfter curveParams pt bits 64 =
      stepNative curveParams pt (evalPt env (accVar n body init ⟨63, by omega⟩))
        (bits[2 * 63]'(by omega)) (bits[2 * 63 + 1]'(by omega)) :=
    accAfter_succ_of_some curveParams pt bits 63 _ h63 (by omega)
  have h_ne64 := all_accAfter_ne curveParams pt bits h_ne 64 le_rfl
  rw [h_acc64] at h_ne64
  have h := h_steps ⟨63, by omega⟩
  simp only [Step.Assumptions, Step.Spec, h_bit] at h
  obtain ⟨h_s, h_c⟩ := h ⟨h_pt, h63_curve, h_bool ⟨2 * 63, by omega⟩,
    h_bool ⟨2 * 63 + 1, by omega⟩, h_ne64⟩
  rw [fin_foldl_eq_last n body init hlen, h_link]
  show accAfter curveParams pt bits 64 = _ ∧ _
  rw [h_acc64]
  exact ⟨h_s, h_c⟩

/-! ## Soundness and completeness. -/

theorem soundness (curveParams : Point.Spec.CurveParams p)
    : Soundness (F p) (Input := Input) (Output := Point.Spec.Point) (main curveParams)
        (Assumptions curveParams) (Spec curveParams) := by
  -- `main` is `@[irreducible]` (see its docstring), so `circuit_proof_start`
  -- cannot auto-unfold it and it must be named here. `Step.Assumptions` /
  -- `Step.Spec` are deliberately left folded: the fold lemmas above consume
  -- them as such.
  circuit_proof_start [main, Step.circuit,
    Point.AddIncompleteUnchecked.circuit, Point.AddIncompleteUnchecked.Assumptions,
    Point.AddIncompleteUnchecked.Spec,
    Point.Double.circuit, Point.Double.Assumptions, Point.Double.Spec]
  obtain ⟨h_pt_curve, h_no2, h_bits, h_native_ne⟩ := h_assumptions
  obtain ⟨h_add, h_double, h_steps⟩ := h_holds
  obtain ⟨h_bits_eval, h_px, h_py⟩ := h_input
  -- Value-level bit lookups.
  have h_bit : ∀ (j : ℕ) (hj : j < 128),
      Expression.eval env (input_var_bits[j]'hj) = input_bits[j]'hj := by
    intro j hj
    have := congrArg (fun v => v[j]'hj) h_bits_eval
    simpa [Vector.getElem_map] using this
  -- p.endo is on the curve (ζ³ = 1).
  have h_endo_curve : (⟨curveParams.ζ * input_pt_x, input_pt_y⟩
      : Point.Spec.Point (F p)).isOnCurve curveParams := by
    simp only [Point.Spec.Point.isOnCurve] at h_pt_curve ⊢
    rw [mul_pow, curveParams.h_small_order, one_mul]
    exact h_pt_curve
  -- The init add's distinct-x condition, from the native chain.
  have h_acc0_ne := all_accAfter_ne curveParams ⟨input_pt_x, input_pt_y⟩ input_bits
    h_native_ne 0 (by omega)
  have h_zx_ne : curveParams.ζ * input_pt_x ≠ input_pt_x := by
    intro h
    apply h_acc0_ne
    simp only [accAfter, initAcc, Point.Spec.Point.endo,
      Point.Spec.Point.add_incomplete, if_pos h]
  obtain ⟨h_add_eq, h_pre_curve⟩ := h_add ⟨h_endo_curve, h_pt_curve, h_zx_ne⟩
  obtain ⟨h_double_eq, h_acc0_curve⟩ := h_double ⟨h_pre_curve, h_no2⟩
  -- The native init chain lands on the circuit's acc₀ expressions.
  have h_acc0 : accAfter curveParams ⟨input_pt_x, input_pt_y⟩ input_bits 0 =
      some ⟨env.get (i₀ + 9 + 3 + 3 + 2) -
          ((env.get (i₀ + 3 + 2) - curveParams.ζ * input_pt_x - input_pt_x) +
            (env.get (i₀ + 3 + 2) - curveParams.ζ * input_pt_x - input_pt_x)),
        env.get (i₀ + 9 + 3 + 3 + 3 + 2) - (env.get (i₀ + 3 + 3 + 2) - input_pt_y)⟩ := by
    simp only [accAfter, initAcc, Point.Spec.Point.endo]
    rw [h_add_eq]
    exact h_double_eq
  -- Chain the 64 `Step.Spec`s along the symbolic accumulator; the fold body,
  -- acc₀ and the loop's wire offset are picked up from `h_steps` by
  -- unification.
  have h := fold_final
    (body := fun acc i => Step.circuit curveParams
      ⟨input_var_bits[2 * i.val]'(by have := i.isLt; omega),
       input_var_bits[2 * i.val + 1]'(by have := i.isLt; omega),
       ⟨input_var_pt_x, input_var_pt_y⟩, acc⟩)
    (n := i₀ + 9 + 12)
    curveParams env input_bits input_var_bits ⟨input_pt_x, input_pt_y⟩ _
    h_bit h_pt_curve h_bits h_native_ne h_steps (fun _ _ => rfl)
    (fun acc i => by simp only [circuit_norm, Step.circuit, evalPt, stepOut, h_px])
    ⟨by simpa only [circuit_norm, evalPt, h_px, h_py] using h_acc0,
     by simpa only [circuit_norm, evalPt, h_px, h_py] using h_acc0_curve⟩
  exact h

theorem completeness (curveParams : Point.Spec.CurveParams p)
    : Completeness (F p) (Input := Input) (Output := Point.Spec.Point) (main curveParams) (Assumptions curveParams) := by
  -- Prover side: discharge `Step.Assumptions` per iteration — curve
  -- membership (inductively from `Step.Spec`), bit booleanity (from
  -- `Assumptions`), and per-step `stepNative ≠ none` extracted from
  -- `groupScaleNative ≠ none` via the `accAfter` helpers above.
  -- `main` is `@[irreducible]` (see its docstring), so `circuit_proof_start`
  -- cannot auto-unfold it and it must be named here.
  circuit_proof_start [main, Step.circuit,
    Point.AddIncompleteUnchecked.circuit, Point.AddIncompleteUnchecked.Assumptions,
    Point.AddIncompleteUnchecked.Spec,
    Point.Double.circuit, Point.Double.Assumptions, Point.Double.Spec]
  obtain ⟨h_pt_curve, h_no2, h_bits, h_native_ne⟩ := h_assumptions
  obtain ⟨h_add_env, h_double_env, h_steps_env⟩ := h_env
  obtain ⟨h_bits_eval, h_px, h_py⟩ := h_input
  -- Value-level bit lookups.
  have h_bit : ∀ (j : ℕ) (hj : j < 128),
      Expression.eval env.toEnvironment (input_var_bits[j]'hj) = input_bits[j]'hj := by
    intro j hj
    have := congrArg (fun v => v[j]'hj) h_bits_eval
    simpa [Vector.getElem_map] using this
  -- p.endo is on the curve (ζ³ = 1).
  have h_endo_curve : (⟨curveParams.ζ * input_pt_x, input_pt_y⟩
      : Point.Spec.Point (F p)).isOnCurve curveParams := by
    simp only [Point.Spec.Point.isOnCurve] at h_pt_curve ⊢
    rw [mul_pow, curveParams.h_small_order, one_mul]
    exact h_pt_curve
  -- The init add's distinct-x condition, from the native chain.
  have h_acc0_ne := all_accAfter_ne curveParams ⟨input_pt_x, input_pt_y⟩ input_bits
    h_native_ne 0 (by omega)
  have h_zx_ne : curveParams.ζ * input_pt_x ≠ input_pt_x := by
    intro h
    apply h_acc0_ne
    simp only [accAfter, initAcc, Point.Spec.Point.endo,
      Point.Spec.Point.add_incomplete, if_pos h]
  obtain ⟨h_add_eq, h_pre_curve⟩ := h_add_env ⟨h_endo_curve, h_pt_curve, h_zx_ne⟩
  obtain ⟨h_double_eq, h_acc0_curve⟩ := h_double_env ⟨h_pre_curve, h_no2⟩
  -- The native init chain lands on the prover's acc₀ expressions.
  have h_acc0 : accAfter curveParams ⟨input_pt_x, input_pt_y⟩ input_bits 0 =
      some ⟨env.get (i₀ + 9 + 3 + 3 + 2) -
          ((env.get (i₀ + 3 + 2) - curveParams.ζ * input_pt_x - input_pt_x) +
            (env.get (i₀ + 3 + 2) - curveParams.ζ * input_pt_x - input_pt_x)),
        env.get (i₀ + 9 + 3 + 3 + 3 + 2) - (env.get (i₀ + 3 + 3 + 2) - input_pt_y)⟩ := by
    simp only [accAfter, initAcc, Point.Spec.Point.endo]
    rw [h_add_eq]
    exact h_double_eq
  -- The symbolic accumulator entering each iteration is `accAfter` there.
  have h_inv := fold_inv
    (body := fun acc i => Step.circuit curveParams
      ⟨input_var_bits[2 * i.val]'(by have := i.isLt; omega),
       input_var_bits[2 * i.val + 1]'(by have := i.isLt; omega),
       ⟨input_var_pt_x, input_var_pt_y⟩, acc⟩)
    (n := i₀ + 9 + 12)
    curveParams env.toEnvironment input_bits input_var_bits
    ⟨input_pt_x, input_pt_y⟩ _ h_bit h_pt_curve h_bits h_native_ne h_steps_env
    (fun _ _ => rfl)
    (fun acc i => by simp only [circuit_norm, Step.circuit, evalPt, stepOut, h_px])
    ⟨by simpa only [circuit_norm, evalPt, h_px, h_py] using h_acc0,
     by simpa only [circuit_norm, evalPt, h_px, h_py] using h_acc0_curve⟩
  -- Assemble: init add assumptions, Double assumptions, and per-iteration
  -- Step assumptions.
  refine ⟨⟨h_endo_curve, h_pt_curve, h_zx_ne⟩, ⟨h_pre_curve, h_no2⟩, ?_⟩
  intro i
  obtain ⟨h_prev, h_prev_curve⟩ := h_inv i.val i.isLt
  have h_acci := accAfter_succ_of_some curveParams ⟨input_pt_x, input_pt_y⟩ input_bits i.val _
    h_prev (by have := i.isLt; omega)
  have h_nei := all_accAfter_ne curveParams ⟨input_pt_x, input_pt_y⟩ input_bits h_native_ne
    (i.val + 1) (by have := i.isLt; omega)
  rw [h_acci] at h_nei
  simp only [Step.Assumptions, h_bit]
  exact ⟨h_pt_curve, h_prev_curve, h_bits ⟨2 * i.val, by have := i.isLt; omega⟩,
    h_bits ⟨2 * i.val + 1, by have := i.isLt; omega⟩, h_nei⟩

def circuit (curveParams : Point.Spec.CurveParams p) : FormalCircuit (F p) Input Point.Spec.Point :=
  { main := main curveParams,
    elaborated := elaborated curveParams,
    requirementsChannelsLawful := by
      simp +arith [main, circuit_norm,
        Point.AddIncompleteUnchecked.circuit, Point.Double.circuit, Step.circuit,
        Step.elaborated]
    Assumptions := Assumptions curveParams
    Spec := Spec curveParams
    soundness := soundness curveParams
    completeness := completeness curveParams }

end Ragu.Circuits.Endoscalar.GroupScale
