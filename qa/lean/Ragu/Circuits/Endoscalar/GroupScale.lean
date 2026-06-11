import Clean.Circuit
import Clean.Circuit.Loops
import Clean.Gadgets.Boolean
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Point.AddIncomplete
import Ragu.Circuits.Point.ConditionalEndo
import Ragu.Circuits.Point.ConditionalNegate
import Ragu.Circuits.Point.Double
import Ragu.Circuits.Point.DoubleAndAddIncomplete
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
`Circuit.foldl` body a one-subcircuit call, so Clean's `ConstantOutput` /
`ConstantLength` synthesis and the `circuit_norm`-tagged foldl lemmas fire
within the default heartbeat budget (the same reason
`NonzeroBank.Scope` needs no `set_option`s).

Non-degeneracy (post-PR-741 NonzeroBank architecture): each
`add_incomplete` / `double_and_add_incomplete` call runs inside its own
`NonzeroBank::scope`, folding every denominator into a running product and
discharging `product ≠ 0` via a trailing `enforce_nonzero` — so the
constraints themselves force the distinct-x conditions; no conditional spec
or threaded nonzero wire. The sub-gadget `Inputs` carry an
`UnconstrainedDep field` inverse hint for the prover-side discharge; this
reimpl passes a default closure (`fun _ => 0`) since hints don't affect the
verifier-side constraint trace. The extraction mirrors this by wrapping each
call in `NonzeroBank::scope`. -/
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
foldl's `circuit_norm` lemmas. -/
namespace Step

/-- One iteration's inputs: the 2-bit pair `(n, e)`, the base point `pt`,
and the running accumulator `acc`. No hint input: the DAA's inverse hint is
computed *inside* `main` from the prover environment, so callers (the foldl
in `GroupScale.main`) stay hint-free. -/
structure Input (F : Type) where
  n : F
  e : F
  pt : Point.Spec.Point F
  acc : Point.Spec.Point F
deriving ProvableStruct

/-- ConditionalNegate + ConditionalEndo build `s` from `(n, e)` and `pt`;
DoubleAndAddIncomplete computes `2·acc + s`; the two trailing
`Element.Mul ⟨_, 1⟩` calls freshen both output coordinates so the chained
accumulator stays a bare wire pair across foldl iterations (without this the
symbolic Expression tree grows exponentially over 64 iterations).

The DAA's `inverse` hint is the inverse of its bank's running product
`(x_q - x_p)·(x_p - x_r)` (P1 = acc, P2 = s in DAA's naming), computed here
from the prover environment — both factors are determined by `acc` and `s`,
including the intermediate `x_r = λ₁² - x_p - x_q`. -/
def main (curveParams : Point.Spec.CurveParams p) (input : Var Input (F p))
    : Circuit (F p) (Var Point.Spec.Point (F p)) := do
  let s_neg ← Point.ConditionalNegate.circuit ⟨input.n, input.pt.x, input.pt.y⟩
  let s ← Point.ConditionalEndo.circuit curveParams ⟨input.e, s_neg.x, s_neg.y⟩
  let acc' ← Point.DoubleAndAddIncomplete.circuit curveParams
    ⟨input.acc, s, fun env =>
      let x_p := env input.acc.x
      let y_p := env input.acc.y
      let x_q := env s.x
      let y_q := env s.y
      let lambda_1 := (y_q - y_p) / (x_q - x_p)
      let x_r := lambda_1 ^ 2 - x_p - x_q
      ((x_q - x_p) * (x_p - x_r))⁻¹⟩
  let fresh_x ← Element.Mul.circuit ⟨acc'.x, 1⟩
  let fresh_y ← Element.Mul.circuit ⟨acc'.y, 1⟩
  return ⟨fresh_x, fresh_y⟩

def Assumptions (curveParams : Point.Spec.CurveParams p)
    (input : Input (F p)) (_data : ProverData (F p)) :=
  input.pt.isOnCurve curveParams ∧
  input.acc.isOnCurve curveParams ∧
  IsBool input.n ∧
  IsBool input.e

/-- Unconditional (post-PR-741 style): the DAA's in-circuit bank discharge
forces the distinct-x conditions, so the constraints can only be satisfied
when the native step succeeds. -/
def Spec (curveParams : Point.Spec.CurveParams p)
    (input : Input (F p)) (output : Point.Spec.Point (F p))
    (_data : ProverData (F p)) :=
  stepNative curveParams input.pt input.acc input.n input.e = some output ∧
  output.isOnCurve curveParams

/-- Prover side: the native step must be non-degenerate (distinct
x-coordinates at both internal additions). Stated via the native model; the
completeness proof unfolds it into the two distinct-x facts and shows the
internally computed inverse hint satisfies the bank-product condition
(`mul_inv_cancel₀` on the nonzero product). -/
def ProverAssumptions (curveParams : Point.Spec.CurveParams p)
    (input : Input (F p)) (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  input.pt.isOnCurve curveParams ∧
  input.acc.isOnCurve curveParams ∧
  IsBool input.n ∧ IsBool input.e ∧
  stepNative curveParams input.pt input.acc input.n input.e ≠ none

/-- Prover-side conclusion: witness generation lands exactly on the native
step. `GroupScale.completeness` uses this to thread the accumulator
correspondence (and curve membership) from one iteration to the next. -/
def ProverSpec (curveParams : Point.Spec.CurveParams p)
    (input : Input (F p)) (out : Point.Spec.Point (F p))
    (_hint : ProverHint (F p)) :=
  stepNative curveParams input.pt input.acc input.n input.e = some out ∧
  out.isOnCurve curveParams

instance elaborated (curveParams : Point.Spec.CurveParams p)
    : ElaboratedCircuit (F p) Input Point.Spec.Point where
  main := main curveParams
  -- CondNegate (3) + CondEndo (3) + DAA (24) + 2 × Mul (3 each) = 36
  localLength _ := 36
  -- The freshened coordinates are the two trailing Mul gates' product wires.
  -- Explicit so the foldl body's `ConstantOutput` synthesis in
  -- `GroupScale.main` is a shallow projection instead of a whnf through the
  -- whole 5-subcircuit body (which exceeds the default heartbeat budget).
  output _ offset :=
    ⟨varFromOffset field (offset + 32), varFromOffset field (offset + 35)⟩
  localLength_eq := by
    simp +arith [main, circuit_norm,
      Point.ConditionalNegate.circuit, Point.ConditionalEndo.circuit,
      Point.DoubleAndAddIncomplete.circuit, Element.Mul.circuit]
  output_eq := by
    simp +arith [main, circuit_norm,
      Point.ConditionalNegate.circuit, Point.ConditionalEndo.circuit,
      Point.DoubleAndAddIncomplete.circuit, Element.Mul.circuit]
  subcircuitsConsistent := by
    simp +arith [main, circuit_norm,
      Point.ConditionalNegate.circuit, Point.ConditionalEndo.circuit,
      Point.DoubleAndAddIncomplete.circuit, Element.Mul.circuit]

omit [NeZero (2 : F p)] in
theorem soundness (curveParams : Point.Spec.CurveParams p) :
    GeneralFormalCircuit.Soundness (F p) (elaborated curveParams)
      (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start [Point.ConditionalNegate.circuit, Point.ConditionalNegate.Assumptions,
    Point.ConditionalNegate.Spec, Point.ConditionalNegate.main,
    Point.ConditionalEndo.circuit, Point.ConditionalEndo.Assumptions,
    Point.ConditionalEndo.Spec, Point.ConditionalEndo.main,
    Boolean.ConditionalSelect.circuit,
    Point.DoubleAndAddIncomplete.circuit, Point.DoubleAndAddIncomplete.Assumptions,
    Point.DoubleAndAddIncomplete.Spec, Point.DoubleAndAddIncomplete.main,
    Element.Divide.circuit, Element.Square.circuit, Element.EnforceNonzero.circuit,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec]
  obtain ⟨h_pt_curve, h_acc_curve, h_n_bool, h_e_bool⟩ := h_assumptions
  obtain ⟨h_neg, h_endo, h_daa, h_fx, h_fy⟩ := h_holds
  have h_sy := h_neg h_n_bool
  have h_sx := h_endo h_e_bool
  -- s is on the curve: y² is invariant under negation, x³ under ζ-scaling.
  have h_s_curve : (⟨input_pt_x + env.get (i₀ + 3 + 2),
      input_pt_y + env.get (i₀ + 2)⟩ : Point.Spec.Point (F p)).isOnCurve curveParams := by
    simp only [Point.Spec.Point.isOnCurve] at h_pt_curve ⊢
    rw [h_sx, h_sy]
    rcases h_n_bool with hn | hn <;> rcases h_e_bool with he | he <;>
      simp only [hn, he, zero_ne_one, if_false, if_true, neg_sq, mul_pow,
        curveParams.h_small_order, one_mul] <;>
      exact h_pt_curve
  obtain ⟨r, h_add1, h_add2, h_out_curve⟩ := h_daa ⟨h_acc_curve, h_s_curve⟩
  -- The freshened output wires equal DAA's output coordinates.
  rw [mul_one] at h_fx h_fy
  rw [h_fx, h_fy]
  refine ⟨?_, h_out_curve⟩
  simp only [stepNative]
  rw [← h_sx, ← h_sy, h_add1]
  exact h_add2

omit [NeZero (2 : F p)] in
theorem completeness (curveParams : Point.Spec.CurveParams p) :
    GeneralFormalCircuit.Completeness (F p) (elaborated curveParams)
      (ProverAssumptions curveParams) (ProverSpec curveParams) := by
  circuit_proof_start [Point.ConditionalNegate.circuit, Point.ConditionalNegate.Assumptions,
    Point.ConditionalNegate.Spec, Point.ConditionalNegate.main,
    Point.ConditionalEndo.circuit, Point.ConditionalEndo.Assumptions,
    Point.ConditionalEndo.Spec, Point.ConditionalEndo.main,
    Boolean.ConditionalSelect.circuit,
    Point.DoubleAndAddIncomplete.circuit, Point.DoubleAndAddIncomplete.Assumptions,
    Point.DoubleAndAddIncomplete.Spec, Point.DoubleAndAddIncomplete.ProverAssumptions,
    Point.DoubleAndAddIncomplete.main,
    Element.Divide.circuit, Element.Square.circuit, Element.EnforceNonzero.circuit,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec]
  obtain ⟨h_pt_curve, h_acc_curve, h_n_bool, h_e_bool, h_step_ne⟩ := h_assumptions
  obtain ⟨h_neg_env, h_endo_env, h_daa_env, h_fx, h_fy⟩ := h_env
  have h_sy := h_neg_env h_n_bool
  have h_sx := h_endo_env h_e_bool
  -- Rewrite the native-step hypothesis in terms of the s wires.
  simp only [stepNative] at h_step_ne
  rw [← h_sx, ← h_sy] at h_step_ne
  -- First addition is non-degenerate: acc.x ≠ s.x.
  have h_add1_ne : (⟨input_acc_x, input_acc_y⟩ : Point.Spec.Point (F p)).add_incomplete
      ⟨input_pt_x + env.get (i₀ + 3 + 2), input_pt_y + env.get (i₀ + 2)⟩ ≠ none := by
    intro h
    rw [h] at h_step_ne
    exact h_step_ne rfl
  have h_x_ne : input_acc_x ≠ input_pt_x + env.get (i₀ + 3 + 2) := by
    intro h
    exact h_add1_ne (by simp only [Point.Spec.Point.add_incomplete, if_pos h])
  have h_sub_ne : input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm h_x_ne)
  have h_add1_eq : (⟨input_acc_x, input_acc_y⟩ : Point.Spec.Point (F p)).add_incomplete
      ⟨input_pt_x + env.get (i₀ + 3 + 2), input_pt_y + env.get (i₀ + 2)⟩ =
      some ⟨((input_pt_y + env.get (i₀ + 2) - input_acc_y) /
               (input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x)) ^ 2 - input_acc_x -
               (input_pt_x + env.get (i₀ + 3 + 2)),
             ((input_pt_y + env.get (i₀ + 2) - input_acc_y) /
               (input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x)) *
               (input_acc_x - (((input_pt_y + env.get (i₀ + 2) - input_acc_y) /
                 (input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x)) ^ 2 - input_acc_x -
                 (input_pt_x + env.get (i₀ + 3 + 2)))) - input_acc_y⟩ := by
    simp only [Point.Spec.Point.add_incomplete, if_neg h_x_ne]
  -- Second addition is non-degenerate: x_r ≠ acc.x.
  rw [h_add1_eq] at h_step_ne
  have h_xr_ne : (((input_pt_y + env.get (i₀ + 2) - input_acc_y) /
      (input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x)) ^ 2 - input_acc_x -
      (input_pt_x + env.get (i₀ + 3 + 2))) ≠ input_acc_x := by
    intro h
    exact h_step_ne (by simp only [Point.Spec.Point.add_incomplete, if_pos h])
  have h_sub2_ne : input_acc_x - (((input_pt_y + env.get (i₀ + 2) - input_acc_y) /
      (input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x)) ^ 2 - input_acc_x -
      (input_pt_x + env.get (i₀ + 3 + 2))) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm h_xr_ne)
  -- s is on the curve: y² is invariant under negation, x³ under ζ-scaling.
  have h_s_curve : (⟨input_pt_x + env.get (i₀ + 3 + 2),
      input_pt_y + env.get (i₀ + 2)⟩ : Point.Spec.Point (F p)).isOnCurve curveParams := by
    simp only [Point.Spec.Point.isOnCurve] at h_pt_curve ⊢
    rw [h_sx, h_sy]
    rcases h_n_bool with hn | hn <;> rcases h_e_bool with he | he <;>
      simp only [hn, he, zero_ne_one, if_false, if_true, neg_sq, mul_pow,
        curveParams.h_small_order, one_mul] <;>
      exact h_pt_curve
  -- The bank-product equation for DAA's internally computed inverse.
  have h_lam_eq : (input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x) *
      ((input_pt_y + env.get (i₀ + 2) - input_acc_y) /
       (input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x)) =
      input_pt_y + env.get (i₀ + 2) - input_acc_y := by
    rw [mul_comm, div_mul_cancel₀ _ h_sub_ne]
  have h_prod_ne : (input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x) *
      (input_acc_x - (((input_pt_y + env.get (i₀ + 2) - input_acc_y) /
        (input_pt_x + env.get (i₀ + 3 + 2) - input_acc_x)) ^ 2 - input_acc_x -
        (input_pt_x + env.get (i₀ + 3 + 2)))) ≠ 0 :=
    mul_ne_zero h_sub_ne h_sub2_ne
  obtain ⟨r, h_add1', h_add2', h_out_curve⟩ :=
    h_daa_env ⟨h_acc_curve, h_s_curve, _, _, h_lam_eq, rfl, mul_inv_cancel₀ h_prod_ne⟩
      ⟨h_acc_curve, h_s_curve⟩
  rw [mul_one] at h_fx h_fy
  rw [h_fx, h_fy]
  refine ⟨⟨h_n_bool, h_e_bool, h_acc_curve, h_s_curve, _, _, h_lam_eq, rfl,
    mul_inv_cancel₀ h_prod_ne⟩, ?_, h_out_curve⟩
  simp only [stepNative]
  rw [← h_sx, ← h_sy, h_add1']
  exact h_add2'

def circuit (curveParams : Point.Spec.CurveParams p) :
    GeneralFormalCircuit (F p) Input Point.Spec.Point where
  elaborated := elaborated curveParams
  Assumptions := Assumptions curveParams
  Spec := Spec curveParams
  ProverAssumptions := ProverAssumptions curveParams
  ProverSpec := ProverSpec curveParams
  soundness := soundness curveParams
  completeness := completeness curveParams

end Step

instance : Inhabited (Var Point.Spec.Point (F p)) := ⟨⟨0, 0⟩⟩

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
  -- acc_pre = p_endo + p. The AddIncomplete bank folds `P2.x - P1.x`
  -- (= pt.x - ζ·pt.x), so its inverse hint is that difference's inverse,
  -- computed from the prover environment.
  let acc_pre ← Point.AddIncomplete.circuit curveParams
    ⟨p_endo, input.pt,
     fun env => (env input.pt.x - curveParams.ζ * env input.pt.x)⁻¹⟩
  -- acc₀ = acc_pre.double()
  let acc_0 ← Point.Double.circuit curveParams acc_pre
  -- 64 iterations, each a single `Step.circuit` subcircuit (so the foldl
  -- body's ConstantOutput/ConstantLength synthesize cheaply). Step computes
  -- its own DAA inverse hint internally — no hint plumbing here.
  Circuit.foldl (.finRange 64) acc_0 fun acc i =>
    Step.circuit curveParams
      ⟨input.bits[2 * i.val]'(by have := i.isLt; omega),
       input.bits[2 * i.val + 1]'(by have := i.isLt; omega),
       input.pt, acc⟩

def Assumptions (curveParams : Point.Spec.CurveParams p) (input : Input (F p)) :=
  input.pt.isOnCurve curveParams ∧
  curveParams.noOrderTwoPoints ∧
  (∀ i : Fin 128, IsBool input.bits[i]) ∧
  input.pt.x ≠ 0 ∧
  curveParams.ζ ≠ 1 ∧
  groupScaleNative curveParams input.pt input.bits ≠ none

def Spec (curveParams : Point.Spec.CurveParams p) (input : Input (F p))
    (output : Point.Spec.Point (F p)) :=
  groupScaleNative curveParams input.pt input.bits = some output ∧
  output.isOnCurve curveParams

instance elaborated (curveParams : Point.Spec.CurveParams p)
    : ElaboratedCircuit (F p) Input Point.Spec.Point where
  main := main curveParams
  -- 15 (AddIncomplete) + 12 (Double) + 64 × 36 (Step) = 2331
  localLength _ := 15 + 12 + 64 * 36
  localLength_eq := by
    simp +arith [main, circuit_norm,
      Point.AddIncomplete.circuit, Point.Double.circuit, Step.circuit]
  subcircuitsConsistent := by
    simp +arith [main, circuit_norm,
      Point.AddIncomplete.circuit, Point.Double.circuit, Step.circuit]

/-! ## Native helpers for the prover-side (completeness) non-degeneracy chain.

Post-PR-741 the sub-gadget specs are unconditional, so *soundness* no longer
needs these: the constraints force the distinct-x conditions and
`groupScaleNative = some output` falls out of the per-step specs.
*Completeness* still extracts each iteration's non-degeneracy from the single
`groupScaleNative ≠ none` premise via these lemmas. -/

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

/-! ## Soundness and completeness. -/

/-- The `circuit_norm` foldl lemmas require `[NeZero m]` for the iteration
count; provide it for the loop's 64 once, instance-locally. -/
private instance : NeZero (64 : ℕ) := ⟨by norm_num⟩

theorem soundness (curveParams : Point.Spec.CurveParams p)
    : Soundness (F p) (elaborated curveParams)
        (Assumptions curveParams) (Spec curveParams) := by
  -- Strategy (Step-bundled, post-PR-741):
  --   1. `circuit_proof_start [Step.circuit, Step.Assumptions, Step.Spec,
  --      Point.AddIncomplete.*, Point.Double.*]` — the foldl collapses via
  --      the `circuit_norm` foldl.soundness lemma into a per-iteration
  --      `Step.Spec` chain.
  --   2. Init: AddIncomplete's unconditional spec gives
  --      `p_endo.add_incomplete pt = some acc_pre ∧ acc_pre.isOnCurve`;
  --      Double's gives `acc_pre.double = some acc_0 ∧ ...`.
  --   3. Inductive invariant `∀ m ≤ 64`: the foldl accumulator at iteration
  --      m is the point with `accAfter m = some it` (each step is exactly
  --      `Step.Spec`, i.e. `stepNative ... = some next`).
  --   4. `groupScaleNative = some output` falls out at m = 64 — the
  --      constraints themselves force every non-degeneracy.
  circuit_proof_start [main, Step.circuit, Step.Assumptions, Step.Spec,
    Point.AddIncomplete.circuit, Point.AddIncomplete.Assumptions, Point.AddIncomplete.Spec,
    Point.AddIncomplete.main,
    Point.Double.circuit, Point.Double.Assumptions, Point.Double.Spec, Point.Double.main,
    Element.Divide.circuit, Element.Square.circuit, Element.EnforceNonzero.circuit,
    Element.Mul.circuit]
  obtain ⟨h_pt_curve, h_no2, h_bits, h_px_ne, h_zeta_ne, h_native_ne⟩ := h_assumptions
  obtain ⟨h_add, h_double, h_step0, h_steps⟩ := h_holds
  obtain ⟨h_bits_eval, _, _⟩ := h_input
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
  obtain ⟨h_add_eq, h_pre_curve⟩ := h_add ⟨h_endo_curve, h_pt_curve⟩
  obtain ⟨h_double_eq, h_acc0_curve⟩ := h_double ⟨h_pre_curve, h_no2⟩
  -- The native init chain lands on the circuit's acc₀ wires.
  have h_acc0 : accAfter curveParams ⟨input_pt_x, input_pt_y⟩ input_bits 0 =
      some ⟨env.get (i₀ + 15 + 3 + 3 + 2) +
          -(env.get (i₀ + 3 + 3 + 2) + -(curveParams.ζ * input_pt_x) + -input_pt_x +
            (env.get (i₀ + 3 + 3 + 2) + -(curveParams.ζ * input_pt_x) + -input_pt_x)),
        env.get (i₀ + 15 + 3 + 3 + 3 + 2) + -(env.get (i₀ + 3 + 3 + 3 + 2) + -input_pt_y)⟩ := by
    simp only [accAfter, initAcc, Point.Spec.Point.endo]
    rw [h_add_eq]
    exact h_double_eq
  -- Inductive invariant: the accumulator wires after iteration m hold
  -- `accAfter (m+1)`, which in particular is `some` and on the curve.
  have h_inv : ∀ m : ℕ, m < 64 →
      accAfter curveParams ⟨input_pt_x, input_pt_y⟩ input_bits (m + 1) =
        some ⟨env.get (i₀ + 15 + 12 + m * 36 + 32), env.get (i₀ + 15 + 12 + m * 36 + 35)⟩ ∧
      (⟨env.get (i₀ + 15 + 12 + m * 36 + 32), env.get (i₀ + 15 + 12 + m * 36 + 35)⟩
        : Point.Spec.Point (F p)).isOnCurve curveParams := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨h_s0, h_c0⟩ := h_step0 ⟨h_pt_curve, h_acc0_curve,
        (by rw [h_bit]; exact h_bits ⟨2 * 0, by omega⟩),
        (by rw [h_bit]; exact h_bits ⟨2 * 0 + 1, by omega⟩)⟩
      refine ⟨?_, by simpa using h_c0⟩
      rw [accAfter_succ_of_some _ _ _ 0 _ h_acc0 (by omega)]
      rw [h_bit (2 * 0) (by omega), h_bit (2 * 0 + 1) (by omega)] at h_s0
      simpa using h_s0
    | succ k ih =>
      intro hm
      obtain ⟨h_prev, h_prev_curve⟩ := ih (by omega)
      obtain ⟨h_sk, h_ck⟩ := h_steps k (by omega) ⟨h_pt_curve, h_prev_curve,
        (by rw [h_bit]; exact h_bits ⟨2 * (k + 1), by omega⟩),
        (by rw [h_bit]; exact h_bits ⟨2 * (k + 1) + 1, by omega⟩)⟩
      refine ⟨?_, h_ck⟩
      rw [accAfter_succ_of_some _ _ _ (k + 1) _ h_prev (by omega)]
      rw [h_bit (2 * (k + 1)) (by omega), h_bit (2 * (k + 1) + 1) (by omega)] at h_sk
      exact h_sk
  obtain ⟨h_64, h_64_curve⟩ := h_inv 63 (by omega)
  exact ⟨h_64, h_64_curve⟩

theorem completeness (curveParams : Point.Spec.CurveParams p)
    : Completeness (F p) (elaborated curveParams) (Assumptions curveParams) := by
  -- Prover side: discharge `Step.ProverAssumptions` per iteration —
  -- curve membership (inductively from Step.Spec), bit booleanity (from
  -- Assumptions), and per-step `stepNative ≠ none` extracted from
  -- `groupScaleNative ≠ none` via the `accAfter` helpers above. The init
  -- AddIncomplete needs `(ζ-1)·p.x ≠ 0` (from `h_zeta_ne_one` + `h_px_ne`).
  circuit_proof_start [main, Step.circuit, Step.Assumptions, Step.Spec,
    Step.ProverAssumptions, Step.ProverSpec,
    Point.AddIncomplete.circuit, Point.AddIncomplete.Assumptions, Point.AddIncomplete.Spec,
    Point.AddIncomplete.ProverAssumptions, Point.AddIncomplete.main,
    Point.Double.circuit, Point.Double.Assumptions, Point.Double.Spec, Point.Double.main,
    Element.Divide.circuit, Element.Square.circuit, Element.EnforceNonzero.circuit,
    Element.Mul.circuit]
  obtain ⟨h_pt_curve, h_no2, h_bits, h_px_ne, h_zeta_ne, h_native_ne⟩ := h_assumptions
  obtain ⟨h_add_env, h_double_env, h_step0_env, h_steps_env⟩ := h_env
  obtain ⟨h_bits_eval, _, _⟩ := h_input
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
  -- The init AddIncomplete denominator: pt.x - ζ·pt.x = pt.x·(1 - ζ) ≠ 0.
  have h_x_ne : input_pt_x - curveParams.ζ * input_pt_x ≠ 0 := by
    have h_factor : input_pt_x - curveParams.ζ * input_pt_x =
        input_pt_x * (1 - curveParams.ζ) := by ring
    rw [h_factor]
    exact mul_ne_zero h_px_ne (sub_ne_zero.mpr (Ne.symm h_zeta_ne))
  obtain ⟨h_add_eq, h_pre_curve⟩ :=
    h_add_env ⟨h_endo_curve, h_pt_curve, mul_inv_cancel₀ h_x_ne⟩ ⟨h_endo_curve, h_pt_curve⟩
  obtain ⟨h_double_eq, h_acc0_curve⟩ := h_double_env ⟨h_pre_curve, h_no2⟩
  -- The native init chain lands on the prover's acc₀ wires.
  have h_acc0 : accAfter curveParams ⟨input_pt_x, input_pt_y⟩ input_bits 0 =
      some ⟨env.get (i₀ + 15 + 3 + 3 + 2) +
          -(env.get (i₀ + 3 + 3 + 2) + -(curveParams.ζ * input_pt_x) + -input_pt_x +
            (env.get (i₀ + 3 + 3 + 2) + -(curveParams.ζ * input_pt_x) + -input_pt_x)),
        env.get (i₀ + 15 + 3 + 3 + 3 + 2) + -(env.get (i₀ + 3 + 3 + 3 + 2) + -input_pt_y)⟩ := by
    simp only [accAfter, initAcc, Point.Spec.Point.endo]
    rw [h_add_eq]
    exact h_double_eq
  -- Iteration 0's non-degeneracy: accAfter 1 ≠ none and accAfter 1 IS this step.
  have h_acc1 := accAfter_succ_of_some curveParams ⟨input_pt_x, input_pt_y⟩
    input_bits 0 _ h_acc0 (by omega)
  have h_ne0 : stepNative curveParams ⟨input_pt_x, input_pt_y⟩
      ⟨env.get (i₀ + 15 + 3 + 3 + 2) +
          -(env.get (i₀ + 3 + 3 + 2) + -(curveParams.ζ * input_pt_x) + -input_pt_x +
            (env.get (i₀ + 3 + 3 + 2) + -(curveParams.ζ * input_pt_x) + -input_pt_x)),
        env.get (i₀ + 15 + 3 + 3 + 3 + 2) + -(env.get (i₀ + 3 + 3 + 3 + 2) + -input_pt_y)⟩
      (input_bits[2 * 0]'(by omega)) (input_bits[2 * 0 + 1]'(by omega)) ≠ none := by
    rw [← h_acc1]
    exact all_accAfter_ne curveParams ⟨input_pt_x, input_pt_y⟩ input_bits h_native_ne 1 (by omega)
  -- Inductive invariant: the prover's accumulator wires after iteration m
  -- hold `accAfter (m+1)`, which is `some` and on the curve.
  have h_inv : ∀ m : ℕ, m < 64 →
      accAfter curveParams ⟨input_pt_x, input_pt_y⟩ input_bits (m + 1) =
        some ⟨env.get (i₀ + 15 + 12 + m * 36 + 32), env.get (i₀ + 15 + 12 + m * 36 + 35)⟩ ∧
      (⟨env.get (i₀ + 15 + 12 + m * 36 + 32), env.get (i₀ + 15 + 12 + m * 36 + 35)⟩
        : Point.Spec.Point (F p)).isOnCurve curveParams := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨_, h_s0, h_c0⟩ := h_step0_env ⟨h_pt_curve, h_acc0_curve,
        (by rw [h_bit]; exact h_bits ⟨2 * 0, by omega⟩),
        (by rw [h_bit]; exact h_bits ⟨2 * 0 + 1, by omega⟩),
        (by rw [h_bit (2 * 0) (by omega), h_bit (2 * 0 + 1) (by omega)]; exact h_ne0)⟩
      refine ⟨?_, by simpa using h_c0⟩
      rw [h_acc1]
      rw [h_bit (2 * 0) (by omega), h_bit (2 * 0 + 1) (by omega)] at h_s0
      simpa using h_s0
    | succ k ih =>
      intro hm
      obtain ⟨h_prev, h_prev_curve⟩ := ih (by omega)
      have h_acck := accAfter_succ_of_some curveParams ⟨input_pt_x, input_pt_y⟩
        input_bits (k + 1) _ h_prev (by omega)
      have h_nek : stepNative curveParams ⟨input_pt_x, input_pt_y⟩
          ⟨env.get (i₀ + 15 + 12 + k * 36 + 32), env.get (i₀ + 15 + 12 + k * 36 + 35)⟩
          (input_bits[2 * (k + 1)]'(by omega)) (input_bits[2 * (k + 1) + 1]'(by omega)) ≠
          none := by
        rw [← h_acck]
        exact all_accAfter_ne curveParams ⟨input_pt_x, input_pt_y⟩ input_bits h_native_ne
          (k + 1 + 1) (by omega)
      obtain ⟨_, h_sk, h_ck⟩ := h_steps_env k (by omega) ⟨h_pt_curve, h_prev_curve,
        (by rw [h_bit]; exact h_bits ⟨2 * (k + 1), by omega⟩),
        (by rw [h_bit]; exact h_bits ⟨2 * (k + 1) + 1, by omega⟩),
        (by
          rw [h_bit (2 * (k + 1)) (by omega), h_bit (2 * (k + 1) + 1) (by omega)]
          exact h_nek)⟩
      refine ⟨?_, h_ck⟩
      rw [h_acck]
      rw [h_bit (2 * (k + 1)) (by omega), h_bit (2 * (k + 1) + 1) (by omega)] at h_sk
      exact h_sk
  -- Assemble: init prover assumptions, Double assumptions, and per-iteration
  -- Step prover assumptions.
  refine ⟨⟨h_endo_curve, h_pt_curve, mul_inv_cancel₀ h_x_ne⟩, ⟨h_pre_curve, h_no2⟩,
    ⟨h_pt_curve, h_acc0_curve,
      (by rw [h_bit]; exact h_bits ⟨2 * 0, by omega⟩),
      (by rw [h_bit]; exact h_bits ⟨2 * 0 + 1, by omega⟩),
      (by rw [h_bit (2 * 0) (by omega), h_bit (2 * 0 + 1) (by omega)]; exact h_ne0)⟩,
    ?_⟩
  intro i hi
  obtain ⟨h_prev, h_prev_curve⟩ := h_inv i (by omega)
  have h_acci := accAfter_succ_of_some curveParams ⟨input_pt_x, input_pt_y⟩
    input_bits (i + 1) _ h_prev (by omega)
  have h_nei : stepNative curveParams ⟨input_pt_x, input_pt_y⟩
      ⟨env.get (i₀ + 15 + 12 + i * 36 + 32), env.get (i₀ + 15 + 12 + i * 36 + 35)⟩
      (input_bits[2 * (i + 1)]'(by omega)) (input_bits[2 * (i + 1) + 1]'(by omega)) ≠
      none := by
    rw [← h_acci]
    exact all_accAfter_ne curveParams ⟨input_pt_x, input_pt_y⟩ input_bits h_native_ne
      (i + 1 + 1) (by omega)
  exact ⟨h_pt_curve, h_prev_curve,
    (by rw [h_bit]; exact h_bits ⟨2 * (i + 1), by omega⟩),
    (by rw [h_bit]; exact h_bits ⟨2 * (i + 1) + 1, by omega⟩),
    (by
      rw [h_bit (2 * (i + 1)) (by omega), h_bit (2 * (i + 1) + 1) (by omega)]
      exact h_nei)⟩

def circuit (curveParams : Point.Spec.CurveParams p) : FormalCircuit (F p) Input Point.Spec.Point :=
  { elaborated curveParams with
    Assumptions := Assumptions curveParams
    Spec := Spec curveParams
    soundness := soundness curveParams
    completeness := completeness curveParams }

end Ragu.Circuits.Endoscalar.GroupScale
