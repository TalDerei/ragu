import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Element.DivNonzero
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Double
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : F p)]

def main (input : Var Spec.Point (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x, y⟩ := input

  -- delta = 3x^2 / 2y
  let double_y := y + y
  let ⟨x2⟩ ← subcircuit Element.Square.circuit ⟨x⟩
  let x2_scaled := (3 : F p) * x2
  let delta ← subcircuit Element.DivNonzero.circuit ⟨x2_scaled, double_y⟩

  -- x3 = delta^2 - 2x
  let double_x := x + x
  let ⟨delta2⟩ ← subcircuit Element.Square.circuit ⟨delta⟩
  let x3 := delta2 - double_x

  -- y3 = delta * (x - x3) - y
  let x_sub_x3 := x - x3
  let delta_x_sub_3 ← subcircuit Element.Mul.circuit ⟨delta, x_sub_x3⟩
  let y3 := delta_x_sub_3 - y

  return ⟨x3, y3⟩

def Assumptions (curveParams : Spec.CurveParams (F p)) (input : Spec.Point (F p)) :=
  input.isOnCurve curveParams ∧
  -- for the circuit to be sound, there must not exist points of order 2 on the curve,
  -- therefore soundness is also conditioned on the following property:
  curveParams.noOrderTwoPoints

def Spec (curveParams : Spec.CurveParams (F p)) (input : Spec.Point (F p)) (output : Spec.Point (F p)) :=
  (match input.double with
  | none => False -- this case never happens
  | some double => output = double)
  ∧
  output.isOnCurve curveParams

instance elaborated : ElaboratedCircuit (F p) Spec.Point Spec.Point where
  main
  localLength _ := 12

theorem soundness (curveParams : Spec.CurveParams (F p)) : Soundness (F p) elaborated (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start
  simp [circuit_norm,
    Element.Square.circuit, Element.Square.Assumptions, Element.Square.Spec,
    Element.DivNonzero.circuit, Element.DivNonzero.Assumptions, Element.DivNonzero.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ] at h_holds ⊢

  obtain ⟨c1, c2, c3, c4⟩ := h_holds

  obtain ⟨h_membership, h_order⟩ := h_assumptions
  have h : input_y + input_y ≠ 0 := by
    have hy : input_y ≠ 0 := h_order ⟨input_x, input_y⟩ h_membership
    rw [← two_mul]
    exact mul_ne_zero (NeZero.ne 2) hy

  simp [h, c1] at c2
  rw [c2] at c3 c4
  rw [c3] at c4
  clear c1 c2

  have hy : input_y ≠ 0 := h_order ⟨input_x, input_y⟩ h_membership
  simp only [Spec.Point.double, if_neg hy]

  constructor
  · rw [c3, c4]
    ring_nf
  · rw [c3, c4]
    have h_d := Lemmas.double_preserves_membership ⟨input_x, input_y⟩ curveParams h_membership h_order
    simp only [Spec.Point.double, if_neg hy] at h_d
    ring_nf at ⊢ h_d
    exact h_d


theorem completeness (curveParams : Spec.CurveParams (F p)) : Completeness (F p) elaborated (Assumptions curveParams) := by
  sorry

def circuit (curveParams : Spec.CurveParams (F p)) : FormalCircuit (F p) Spec.Point Spec.Point :=
  {
    elaborated with
    Assumptions := Assumptions curveParams,
    Spec := Spec curveParams,
    soundness := soundness curveParams,
    completeness := completeness curveParams
  }

end Ragu.Circuits.Point.Double
