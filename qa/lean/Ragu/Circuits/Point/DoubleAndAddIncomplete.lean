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

Result: (x_s, y_s) = 2·P1 + P2. Two DivNonzero subcircuits (one hint each)
+ two Square subcircuits + one Mul subcircuit = 15 wires. -/
def main (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
         (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (input : Var Inputs (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩ := input

  -- λ₁ = (y₂ - y₁) / (x₂ - x₁)
  let tmp1 := x2 - x1
  let lambda_1 ← Element.DivNonzero.circuit hintReader1 ⟨y2 - y1, tmp1⟩

  -- x_r = λ₁² - x₁ - x₂
  let lambda_1_sq ← Element.Square.circuit lambda_1
  let x_r := lambda_1_sq - x1 - x2

  -- λ₂ = 2y₁ / (x₁ - x_r) - λ₁
  let tmp2 := x1 - x_r
  let lambda_2_half ← Element.DivNonzero.circuit hintReader2 ⟨y1 + y1, tmp2⟩
  let lambda_2 := lambda_2_half - lambda_1

  -- x_s = λ₂² - x_r - x₁
  let lambda_2_sq ← Element.Square.circuit lambda_2
  let x_s := lambda_2_sq - x_r - x1

  -- y_s = λ₂ (x₁ - x_s) - y₁
  let lambda_2_x_diff ← Element.Mul.circuit ⟨lambda_2, x1 - x_s⟩
  let y_s := lambda_2_x_diff - y1

  return ⟨x_s, y_s⟩

/-- Completeness needs both DivNonzero hints to describe valid witnesses
(quotient and denominator agree with the respective inputs) and the two
intermediate non-degeneracies: `x₁ ≠ x₂` (for the first slope) and
`x₁ ≠ x_r` (for the second slope, after computing the midpoint
x-coordinate). `x₁ ≠ x₂` is asserted here directly because the first
DivNonzero's `GeneralAssumptions` gives only the weaker `x₂-x₁ ≠ 0 ∨
y₂-y₁ = 0`, which isn't enough to discharge DivNonzero's `Spec` premise
when bridging the symbolic quotient to the witness. -/
def Assumptions (_curveParams : Spec.CurveParams p)
    (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (input : Inputs (F p)) (data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let x_r := ((input.P2.y - input.P1.y) / (input.P2.x - input.P1.x))^2
    - input.P1.x - input.P2.x
  input.P1.x ≠ input.P2.x ∧
  Element.DivNonzero.Assumptions hintReader1
    ⟨input.P2.y - input.P1.y, input.P2.x - input.P1.x⟩ data hint ∧
  Element.DivNonzero.Assumptions hintReader2
    ⟨input.P1.y + input.P1.y, input.P1.x - x_r⟩ data hint

/-- The output is `2·P1 + P2` under the curve-membership preconditions and
the two non-degeneracy assumptions. Stated via `add_incomplete` twice:
`r = P1 + P2`, then `s = r + P1 = 2P1 + P2`. -/
def Spec (curveParams : Spec.CurveParams p) (input : Inputs (F p))
    (output : Spec.Point (F p)) (_data : ProverData (F p)) :=
  input.P1.isOnCurve curveParams →
  input.P2.isOnCurve curveParams →
  input.P1.x ≠ input.P2.x →
  (match input.P1.add_incomplete input.P2 with
   | none => False
   | some r =>
     r.x ≠ input.P1.x →
     ((match r.add_incomplete input.P1 with
       | none => False
       | some s => output = s)
      ∧ output.isOnCurve curveParams))

instance elaborated (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    : ElaboratedCircuit (F p) Inputs Spec.Point where
  main := main hintReader1 hintReader2
  localLength _ := 15

set_option maxHeartbeats 800000 in
theorem soundness (curveParams : Spec.CurveParams p)
    (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader1 hintReader2)
        (Spec curveParams) := by
  circuit_proof_start
  simp [circuit_norm,
    Element.Square.circuit, Element.Square.Assumptions, Element.Square.Spec,
    Element.DivNonzero.circuit, Element.DivNonzero.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ] at h_holds ⊢
  obtain ⟨c1, c2, c3, c4, c5⟩ := h_holds
  intro h_P1_mem h_P2_mem h_xne
  -- Specialize c1 using `x₁ ≠ x₂` (equivalent to `x₂ + -x₁ ≠ 0`).
  have h_xne' : ¬input_P2_x + -input_P1_x = 0 := by
    intro h; rw [add_neg_eq_zero] at h; exact h_xne h.symm
  specialize c1 (Or.inl h_xne')
  -- Rewrite Sq₁ via c1, c2: eval(Sq₁) = ((y2-y1)/(x2-x1))^2.
  rw [c1] at c2
  -- At this point `P1.add_incomplete P2` still shows up in the goal. Unfold
  -- it using h_xne.
  simp only [Spec.Point.add_incomplete, if_neg h_xne]
  intro h_rx_ne
  -- c3's premise: `x₁ - r.x ≠ 0 ∨ 2y₁ ≠ 0`. We discharge the disjunction
  -- with the left disjunct, deriving `x₁ - r.x ≠ 0` from h_rx_ne (plus the
  -- c2 rewrite bridging Sq₁ to λ₁²).
  have h_r_premise : input_P1_x + (input_P2_x + (input_P1_x +
        -Expression.eval env
          (Element.Square.main
            (Element.DivNonzero.main hintReader1
              { x := input_var_P2_y - input_var_P1_y,
                y := input_var_P2_x - input_var_P1_x } i₀).1
            (i₀ + 3)).1)) ≠ 0 := by
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
      have : input_P1_x + (input_P2_x + (input_P1_x +
          -((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2)) = 0 := h
      linear_combination -this
    linear_combination hq
  specialize c3 (Or.inl h_r_premise)
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
  -- Unfold the inner add_incomplete's if using h_rx_ne.
  rw [if_neg h_rx_ne]
  -- Prove the two coordinate equalities individually, then assemble.
  have h_x : Expression.eval env
        (Element.Square.main
          ((Element.DivNonzero.main hintReader2
                { x := input_var_P1_y + input_var_P1_y,
                  y :=
                    input_var_P1_x -
                      ((Element.Square.main
                              (Element.DivNonzero.main hintReader1
                                  { x := input_var_P2_y - input_var_P1_y,
                                    y := input_var_P2_x - input_var_P1_x }
                                  i₀).1
                              (i₀ + 3)).1 -
                          input_var_P1_x -
                        input_var_P2_x) }
                (i₀ + 3 + 3)).1 -
            (Element.DivNonzero.main hintReader1
                { x := input_var_P2_y - input_var_P1_y,
                  y := input_var_P2_x - input_var_P1_x } i₀).1)
          (i₀ + 3 + 3 + 3)).1 +
      (input_P2_x + (input_P1_x + -Expression.eval env
        (Element.Square.main
          (Element.DivNonzero.main hintReader1
            { x := input_var_P2_y - input_var_P1_y,
              y := input_var_P2_x - input_var_P1_x } i₀).1
          (i₀ + 3)).1)) + -input_P1_x = s.x := by
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
  have h_y : Expression.eval env
      (Element.Mul.main
        {
          x :=
            (Element.DivNonzero.main hintReader2
                  { x := input_var_P1_y + input_var_P1_y,
                    y :=
                      input_var_P1_x -
                        ((Element.Square.main
                                (Element.DivNonzero.main hintReader1
                                    { x := input_var_P2_y - input_var_P1_y,
                                      y := input_var_P2_x - input_var_P1_x }
                                    i₀).1
                                (i₀ + 3)).1 -
                            input_var_P1_x -
                          input_var_P2_x) }
                  (i₀ + 3 + 3)).1 -
              (Element.DivNonzero.main hintReader1
                  { x := input_var_P2_y - input_var_P1_y,
                    y := input_var_P2_x - input_var_P1_x } i₀).1,
          y :=
            input_var_P1_x -
              ((Element.Square.main
                      ((Element.DivNonzero.main hintReader2
                            { x := input_var_P1_y + input_var_P1_y,
                              y :=
                                input_var_P1_x -
                                  ((Element.Square.main
                                          (Element.DivNonzero.main hintReader1
                                              { x := input_var_P2_y - input_var_P1_y,
                                                y := input_var_P2_x - input_var_P1_x }
                                              i₀).1
                                          (i₀ + 3)).1 -
                                      input_var_P1_x -
                                    input_var_P2_x) }
                            (i₀ + 3 + 3)).1 -
                        (Element.DivNonzero.main hintReader1
                            { x := input_var_P2_y - input_var_P1_y,
                              y := input_var_P2_x - input_var_P1_x }
                            i₀).1)
                      (i₀ + 3 + 3 + 3)).1 -
                  ((Element.Square.main
                          (Element.DivNonzero.main hintReader1
                              { x := input_var_P2_y - input_var_P1_y,
                                y := input_var_P2_x - input_var_P1_x }
                              i₀).1
                          (i₀ + 3)).1 -
                      input_var_P1_x -
                    input_var_P2_x) -
                input_var_P1_x) }
        (i₀ + 3 + 3 + 3 + 3)).1 +
      -input_P1_y = s.y := by
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
    show Spec.Point.mk _ _ = s
    rw [show s = ⟨s.x, s.y⟩ from rfl]
    exact Spec.Point.mk.injEq _ _ _ _ |>.mpr ⟨h_x, h_y⟩
  · -- Output.isOnCurve
    show Spec.Point.isOnCurve ⟨_, _⟩ curveParams
    simp only [Spec.Point.isOnCurve]
    rw [h_x, h_y]
    have := h_s_mem
    simp only [Spec.Point.isOnCurve] at this
    exact this

set_option maxHeartbeats 800000 in
theorem completeness (curveParams : Spec.CurveParams p)
    (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader1 hintReader2)
        (Assumptions curveParams hintReader1 hintReader2) := by
  circuit_proof_start [
    Element.Square.circuit, Element.Square.Assumptions,
    Element.DivNonzero.circuit, Element.DivNonzero.Assumptions,
    Element.Mul.circuit, Element.Mul.Assumptions
  ]
  simp only [Element.DivNonzero.Spec] at h_env
  simp only [sub_eq_add_neg] at h_assumptions
  obtain ⟨h_xne, h_a1, h_a2⟩ := h_assumptions
  obtain ⟨h_div1_spec, h_sq1_spec, _⟩ := h_env
  -- Discharge DivNonzero#1's outer `Assumptions → ...` via h_a1, then its
  -- inner `(y ≠ 0 ∨ x ≠ 0) → out = x/y` via `x₁ ≠ x₂`.
  have h_div1 := h_div1_spec h_a1
  have h_prem : input_P2_x + -input_P1_x ≠ 0 ∨ input_P2_y + -input_P1_y ≠ 0 := by
    left
    intro h
    rw [add_neg_eq_zero] at h
    exact h_xne h.symm
  have h_div1_eq := h_div1.1 h_prem
  simp only [Element.Square.Spec] at h_sq1_spec
  -- Goal: (hintReader1 GeneralAssumptions) ∧ (hintReader2 GeneralAssumptions at env x_r).
  -- First conjunct is `h_a1` directly; second needs the env-level
  -- `Square(lambda_1)` → `lambda_1^2` → `((y2-y1)/(x2-x1))^2` rewrite chain.
  rw [h_sq1_spec, h_div1_eq]
  exact ⟨h_a1, h_a2⟩

def circuit (curveParams : Spec.CurveParams p)
    (hintReader1 : ProverHint (F p) → Core.AllocMul.Row (F p))
    (hintReader2 : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) Inputs Spec.Point :=
  { elaborated hintReader1 hintReader2 with
    Assumptions := Assumptions curveParams hintReader1 hintReader2,
    Spec := Spec curveParams,
    soundness := soundness curveParams hintReader1 hintReader2,
    completeness := completeness curveParams hintReader1 hintReader2 }

end Ragu.Circuits.Point.DoubleAndAddIncomplete
