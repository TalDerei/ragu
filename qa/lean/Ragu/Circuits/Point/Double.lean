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
  let x2 ← Element.Square.circuit x
  let x2_scaled := (3 : F p) * x2
  let delta ← Element.DivNonzero.circuit { x := x2_scaled, y := double_y }

  -- x3 = delta^2 - 2x
  let double_x := x + x
  let delta2 ← Element.Square.circuit delta
  let x3 := delta2 - double_x

  -- y3 = delta * (x - x3) - y
  let x_sub_x3 := x - x3
  let delta_x_sub_3 ← Element.Mul.circuit ⟨delta, x_sub_x3⟩
  let y3 := delta_x_sub_3 - y

  return ⟨x3, y3⟩

def Assumptions (curveParams : Spec.CurveParams p)
    (input : Spec.Point (F p)) :=
  input.isOnCurve curveParams ∧
  curveParams.noOrderTwoPoints

def Spec (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) (output : Spec.Point (F p)) :=
  input.double = some output ∧
  output.isOnCurve curveParams

instance elaborated :
    ElaboratedCircuit (F p) Spec.Point Spec.Point where
  main
  localLength _ := 12

theorem soundness (curveParams : Spec.CurveParams p) :
    Soundness (F p) elaborated (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start [
    Element.Square.circuit, Element.Square.Assumptions, Element.Square.Spec,
    Element.DivNonzero.circuit, Element.DivNonzero.Assumptions, Element.DivNonzero.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  obtain ⟨c1, c2, c3, c4⟩ := h_holds
  obtain ⟨h_membership, h_order⟩ := h_assumptions

  have hy : input_y ≠ 0 := h_order ⟨input_x, input_y⟩ h_membership
  have h2y_ne : input_y + input_y ≠ 0 := by
    rw [← two_mul]; exact mul_ne_zero (NeZero.ne 2) hy

  -- Chain subcircuit specs through hypotheses (like AddIncomplete soundness)
  have h_delta := c2 (Or.inl h2y_ne)
  rw [c1] at h_delta
  rw [h_delta] at c3 c4
  rw [c3] at c4
  simp only [Spec.Point.double, if_neg hy]

  -- Substitute simplified subcircuit outputs into goal
  constructor
  · simp only [Option.some.injEq, Spec.Point.mk.injEq]
    rw [c3, c4]
    constructor <;> ring_nf
  · have h_d := Lemmas.double_preserves_membership ⟨input_x, input_y⟩ curveParams h_membership h_order
    simp only [Spec.Point.double, if_neg hy] at h_d
    simp only [Spec.Point.isOnCurve] at h_d ⊢
    rw [c3, c4]
    ring_nf at ⊢ h_d
    exact h_d

theorem completeness (curveParams : Spec.CurveParams p) :
    Completeness (F p) elaborated (Assumptions curveParams) := by
  circuit_proof_start [
    Element.Square.circuit, Element.Square.Assumptions,
    Element.DivNonzero.circuit,
    Element.Mul.circuit, Element.Mul.Assumptions
  ]
  rw [← two_mul]
  exact mul_ne_zero (NeZero.ne 2)
    (h_assumptions.2 ⟨input_x, input_y⟩ h_assumptions.1)

def circuit (curveParams : Spec.CurveParams p) : FormalCircuit (F p) Spec.Point Spec.Point where
  elaborated
  Assumptions := Assumptions curveParams
  Spec := Spec curveParams
  soundness := soundness curveParams
  completeness := completeness curveParams

end Ragu.Circuits.Point.Double
