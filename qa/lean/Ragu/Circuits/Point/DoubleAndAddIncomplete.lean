import Clean.Circuit
import Clean.Utils.Primes
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Element.DivNonzero
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.DoubleAndAddIncomplete
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  P1 : Spec.Point F  -- the point to be doubled (Rust's `self`)
  P2 : Spec.Point F  -- the point to be added once (Rust's `other`)
deriving ProvableStruct

/-- `Point::double_and_add_incomplete(other)` computes `2·P1 + P2` via the
zcash optimization that avoids materializing `P1 + P2` explicitly:

- λ₁ = (y₂ - y₁) / (x₂ - x₁) — slope through P1 and P2.
- x_r = λ₁² - x₁ - x₂ — x-coord of P1 + P2.
- λ₂ = 2y₁ / (x₁ - x_r) - λ₁ — slope through (P1 + P2) and P1 (derived).
- x_s = λ₂² - x_r - x₁.
- y_s = λ₂ (x₁ - x_s) - y₁.

Result: (x_s, y_s) = 2·P1 + P2. Two DivNonzero subcircuits
+ two Square subcircuits + one Mul subcircuit = 15 wires. -/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩ := input

  -- λ₁ = (y₂ - y₁) / (x₂ - x₁)
  let lambda_1 ← Element.DivNonzero.circuit ⟨y2 - y1, x2 - x1⟩

  -- x_r = λ₁² - x₁ - x₂
  let lambda_1_sq ← Element.Square.circuit lambda_1
  let x_r := lambda_1_sq - x1 - x2

  -- λ₂ = 2y₁ / (x₁ - x_r) - λ₁
  let lambda_2_half ← Element.DivNonzero.circuit ⟨y1 + y1, x1 - x_r⟩
  let lambda_2 := lambda_2_half - lambda_1

  -- x_s = λ₂² - x_r - x₁
  let lambda_2_sq ← Element.Square.circuit lambda_2
  let x_s := lambda_2_sq - x_r - x1

  -- y_s = λ₂ (x₁ - x_s) - y₁
  let lambda_2_x_diff ← Element.Mul.circuit ⟨lambda_2, x1 - x_s⟩
  let y_s := lambda_2_x_diff - y1

  return ⟨x_s, y_s⟩

/-- Verifier-side assumptions: both inputs are on curve and the first slope is
well-defined. -/
def Assumptions (curveParams : Spec.CurveParams p)
    (input : Inputs (F p)) (_data : ProverData (F p)) :=
  input.P1.isOnCurve curveParams ∧
  input.P2.isOnCurve curveParams ∧
  input.P1.x ≠ input.P2.x

/-- Completeness needs the two intermediate non-degeneracies:
`x₁ ≠ x₂` (for the first slope) and
`x₁ ≠ x_r` (for the second slope, after computing the midpoint
x-coordinate). -/
def ProverAssumptions (curveParams : Spec.CurveParams p)
    (input : Inputs (F p)) (data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  Assumptions curveParams input data ∧
  ∃ r, input.P1.add_incomplete input.P2 = some r ∧ r.x ≠ input.P1.x

/-- The output is `2·P1 + P2` under the curve-membership preconditions and
the two non-degeneracy assumptions. Stated via `add_incomplete` twice:
`r = P1 + P2`, then `s = r + P1 = 2P1 + P2`. -/
def Spec (curveParams : Spec.CurveParams p) (input : Inputs (F p))
    (output : Spec.Point (F p)) (_data : ProverData (F p)) :=
  ∃ r, input.P1.add_incomplete input.P2 = some r ∧
    (r.x ≠ input.P1.x →
      r.add_incomplete input.P1 = some output ∧
      output.isOnCurve curveParams)

instance elaborated : ElaboratedCircuit (F p) Inputs Spec.Point where
  main
  localLength _ := 15

set_option maxHeartbeats 800000 in
theorem soundness (curveParams : Spec.CurveParams p)
    : GeneralFormalCircuit.Soundness (F p) elaborated
        (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start [
    Element.Square.circuit, Element.Square.Assumptions, Element.Square.Spec,
    Element.DivNonzero.circuit, Element.DivNonzero.Assumptions, Element.DivNonzero.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  simp only [neg_add_rev, neg_neg] at h_holds ⊢
  obtain ⟨c1, c2, c3, c4, c5⟩ := h_holds
  obtain ⟨h_P1_mem, h_P2_mem, h_xne⟩ := h_assumptions
  -- Specialize c1 using `x₁ ≠ x₂` (equivalent to `x₂ + -x₁ ≠ 0`).
  have h_xne' : ¬input_P2_x + -input_P1_x = 0 := by
    intro h; rw [add_neg_eq_zero] at h; exact h_xne h.symm
  specialize c1 (Or.inl h_xne')
  -- Rewrite Sq₁ via c1, c2: eval(Sq₁) = ((y2-y1)/(x2-x1))^2.
  rw [c1] at c2
  let rOpt := (⟨input_P1_x, input_P1_y⟩ : Spec.Point (F p)).add_incomplete ⟨input_P2_x, input_P2_y⟩
  rcases h_rOpt : rOpt with _ | r
  · simp [rOpt, Spec.Point.add_incomplete, h_xne] at h_rOpt
  refine ⟨r, h_rOpt, ?_⟩
  simp only [rOpt, Spec.Point.add_incomplete, if_neg h_xne, Option.some.injEq] at h_rOpt
  subst r
  intro h_rx_ne
  have h_rx_ne :
      ((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2 -
          input_P1_x - input_P2_x ≠ input_P1_x := h_rx_ne
  simp only [Spec.Point.add_incomplete, if_neg h_rx_ne, Option.some.injEq]
  -- The remaining branch is the non-degenerate second add.
  -- c3's premise: `x₁ - r.x ≠ 0 ∨ 2y₁ ≠ 0`. We discharge the disjunction
  -- with the left disjunct, deriving `x₁ - r.x ≠ 0` from h_rx_ne (plus the
  -- c2 rewrite bridging Sq₁ to λ₁²).
  specialize c3 (Or.inl (by
    intro h
    rw [c2] at h
    apply h_rx_ne
    -- Bridge `+ -x` to `- x` in the quotient inside h.
    have hh : ((input_P2_y + -input_P1_y) / (input_P2_x + -input_P1_x))^2 =
              ((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x))^2 := by
      congr 1
      all_goals ring
    rw [hh] at h
    -- h : x1 + (x2 + (x1 + -q)) = 0, i.e., 2 x1 + x2 - q = 0, so q = 2 x1 + x2.
    -- Goal: q - x1 - x2 = x1. Algebraically: q - x1 - x2 = 2x1 + x2 - x1 - x2 = x1.
    have hq : ((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x))^2 =
              input_P1_x + input_P2_x + input_P1_x := by
      linear_combination -h
    linear_combination hq))
  rw [c2] at c3
  rw [c1] at c4
  rw [c1, c2] at c5
  -- Obtain membership of the intermediate sum r = P1 + P2.
  have h_r_mem :=
    Lemmas.add_incomplete_preserves_membership
      ⟨input_P1_x, input_P1_y⟩ ⟨input_P2_x, input_P2_y⟩ curveParams h_xne h_P1_mem h_P2_mem
  simp only [Spec.Point.add_incomplete, if_neg h_xne] at h_r_mem
  -- Name r := P1 + P2.
  set r : Spec.Point (F p) :=
    ⟨((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2 - input_P1_x - input_P2_x,
     ((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) *
       (input_P1_x -
         (((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2 - input_P1_x - input_P2_x)) -
       input_P1_y⟩ with hr_def
  change r.isOnCurve curveParams at h_r_mem
  have h_rx_ne_P1 : r.x ≠ input_P1_x := h_rx_ne
  -- Obtain membership of s := r + P1.
  have h_s_mem :=
    Lemmas.add_incomplete_preserves_membership
      r ⟨input_P1_x, input_P1_y⟩ curveParams h_rx_ne_P1 h_r_mem h_P1_mem
  simp only [Spec.Point.add_incomplete, if_neg h_rx_ne_P1] at h_s_mem
  -- Name s := r + P1.
  set s : Spec.Point (F p) :=
    ⟨((input_P1_y - r.y) / (input_P1_x - r.x)) ^ 2 - r.x - input_P1_x,
     ((input_P1_y - r.y) / (input_P1_x - r.x)) *
       (r.x - (((input_P1_y - r.y) / (input_P1_x - r.x)) ^ 2 - r.x - input_P1_x)) - r.y⟩ with hs_def
  change s.isOnCurve curveParams at h_s_mem
  -- Prove the two coordinate equalities individually, then assemble.
  have h_x :
      env.get (i₀ + 3 + 3 + 3 + 2) +
        (input_P2_x + (input_P1_x + -env.get (i₀ + 3 + 2))) + -input_P1_x = s.x := by
    simp only [hs_def, hr_def]; rw [c4, c3, c2]
    have e1 : input_P2_y + -input_P1_y = input_P2_y - input_P1_y := by ring
    have e2 : input_P2_x + -input_P1_x = input_P2_x - input_P1_x := by ring
    rw [e1, e2]
    -- `ring` in Lean's Mathlib handles division in fields, but here the nested
    -- quotient with a variable denominator trips it up. Extract the
    -- denominator `D` (which we know is nonzero by h_rx_ne / h_rx_ne_P1) and
    -- use `field_simp` to clear it.
    set L : F p := (input_P2_y - input_P1_y) / (input_P2_x - input_P1_x) with hL
    have hD : input_P1_x - (L ^ 2 - input_P1_x - input_P2_x) ≠ 0 := by
      intro heq
      apply h_rx_ne
      linear_combination -heq
    have hD' : input_P1_x + (input_P2_x + (input_P1_x + -L ^ 2)) ≠ 0 := by
      intro heq
      apply hD
      linear_combination heq
    field_simp
    ring
  have h_y :
      env.get (i₀ + 3 + 3 + 3 + 3 + 2) + -input_P1_y = s.y := by
    simp only [hs_def, hr_def]
    rw [c5, c4, c3]
    -- Same divisional ring issue as in h_x; bridge `+-` form and apply field_simp.
    have e1 : input_P2_y + -input_P1_y = input_P2_y - input_P1_y := by ring
    have e2 : input_P2_x + -input_P1_x = input_P2_x - input_P1_x := by ring
    rw [e1, e2]
    set L : F p := (input_P2_y - input_P1_y) / (input_P2_x - input_P1_x) with hL
    have hD : input_P1_x - (L ^ 2 - input_P1_x - input_P2_x) ≠ 0 := by
      intro heq
      apply h_rx_ne
      linear_combination -heq
    have hD' : input_P1_x + (input_P2_x + (input_P1_x + -L ^ 2)) ≠ 0 := by
      intro heq
      apply hD
      linear_combination heq
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · -- Output point = s
    rw [show s = ⟨s.x, s.y⟩ from rfl]
    exact (Spec.Point.mk.injEq _ _ _ _ |>.mpr ⟨h_x, h_y⟩).symm
  · -- Output.isOnCurve
    show Spec.Point.isOnCurve ⟨_, _⟩ curveParams
    simp only [Spec.Point.isOnCurve]
    rw [h_x, h_y]
    have := h_s_mem
    simp only [Spec.Point.isOnCurve] at this
    exact this

set_option maxHeartbeats 800000 in
theorem completeness (curveParams : Spec.CurveParams p)
    : GeneralFormalCircuit.Completeness (F p) elaborated
        (ProverAssumptions curveParams) (fun _ _ _ => True) := by
  circuit_proof_start [
    Element.Square.circuit, Element.Square.Assumptions,
    Element.DivNonzero.circuit,
    Element.Mul.circuit, Element.Mul.Assumptions
  ]
  simp only [Element.DivNonzero.Spec] at h_env
  obtain ⟨⟨_, _, h_xne⟩, r, h_add, h_a2⟩ := h_assumptions
  simp only [Spec.Point.add_incomplete, if_neg h_xne, Option.some.injEq, sub_eq_add_neg] at h_add
  subst r
  obtain ⟨h_div1_spec, h_sq1_spec, _⟩ := h_env
  have h_a1 : input_P2_x + -input_P1_x ≠ 0 := by
    intro h
    rw [add_neg_eq_zero] at h
    exact h_xne h.symm
  have h_prem : input_P2_x + -input_P1_x ≠ 0 ∨ input_P2_y + -input_P1_y ≠ 0 :=
    Or.inl h_a1
  have h_div1 := h_div1_spec h_a1
  have h_div1_eq := h_div1 h_prem
  simp only [Element.Square.Spec] at h_sq1_spec
  -- Goal: first DivNonzero assumption and second DivNonzero assumption at env x_r.
  -- First conjunct follows from `x₁ ≠ x₂`; second needs the env-level
  -- `Square(lambda_1)` → `lambda_1^2` → `((y2-y1)/(x2-x1))^2` rewrite chain.
  rw [h_sq1_spec, h_div1_eq]
  exact ⟨h_a1, by
    intro h
    rw [add_neg_eq_zero] at h
    exact h_a2 h.symm⟩

def circuit (curveParams : Spec.CurveParams p) :
    GeneralFormalCircuit (F p) Inputs Spec.Point where
  elaborated
  Assumptions := Assumptions curveParams
  Spec := Spec curveParams
  ProverAssumptions := ProverAssumptions curveParams
  soundness := soundness curveParams
  completeness := completeness curveParams

end Ragu.Circuits.Point.DoubleAndAddIncomplete
