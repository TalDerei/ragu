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
  -- Square(x) → x²
  let ⟨x2⟩ ← Element.Square.circuit ⟨x⟩
  -- DivNonzero(3x², 2y) → delta
  let delta ← Element.DivNonzero.circuit ⟨(3 : F p) * x2, y + y⟩
  -- Square(delta) → delta²
  let ⟨delta2⟩ ← Element.Square.circuit ⟨delta⟩
  let x3 := delta2 - (x + x)
  -- Mul(delta, x - x3)
  let y3_part ← Element.Mul.circuit ⟨delta, x - x3⟩
  return ⟨x3, y3_part - y⟩

def Assumptions (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) (_data : ProverData (F p)) :=
  input.isOnCurve curveParams ∧
  -- for the circuit to be sound, there must not exist points of order 2 on the curve,
  -- therefore soundness is also conditioned on the following property:
  curveParams.noOrderTwoPoints

-- Spec is conditional on curve membership and no order-2 points
def Spec (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) (output : Spec.Point (F p)) (_data : ProverData (F p)) :=
  input.isOnCurve curveParams →
  curveParams.noOrderTwoPoints →
  (match input.double with
  | none => False -- this case never happens
  | some double => output = double)
  ∧
  output.isOnCurve curveParams

instance elaborated : ElaboratedCircuit (F p) Spec.Point Spec.Point where
  main
  localLength _ := 12

theorem soundness (curveParams : Spec.CurveParams p) : GeneralFormalCircuit.Soundness (F p) elaborated (Spec curveParams) := by
  circuit_proof_start
  simp [circuit_norm,
    Element.Square.circuit, Element.Square.Assumptions, Element.Square.Spec,
    Element.DivNonzero.circuit, Element.DivNonzero.Assumptions, Element.DivNonzero.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ] at h_holds ⊢
  obtain ⟨c1, c2, c3, c4⟩ := h_holds

  intro h_membership h_order
  have hy : input_y ≠ 0 := h_order ⟨input_x, input_y⟩ h_membership
  have h2y_ne : input_y + input_y ≠ 0 := by
    rw [← two_mul]; exact mul_ne_zero (NeZero.ne 2) hy

  -- Chain subcircuit specs through hypotheses (like AddIncomplete soundness)
  have h_delta := c2 h2y_ne
  rw [c1] at h_delta
  rw [h_delta] at c3 c4
  rw [c3] at c4
  simp only [Spec.Point.double, if_neg hy]

  -- Substitute simplified subcircuit outputs into goal
  constructor
  · simp only [Spec.Point.mk.injEq]
    rw [c3, c4]
    constructor <;> ring
  · have h_d := Lemmas.double_preserves_membership ⟨input_x, input_y⟩ curveParams h_membership h_order
    simp only [Spec.Point.double, if_neg hy] at h_d
    simp only [Spec.Point.isOnCurve] at h_d ⊢
    rw [c3, c4]
    ring_nf at ⊢ h_d
    exact h_d

theorem completeness (curveParams : Spec.CurveParams p) : GeneralFormalCircuit.Completeness (F p) elaborated (Assumptions curveParams) := by
  circuit_proof_start [
    Element.Square.circuit, Element.Square.Assumptions,
    Element.DivNonzero.circuit, Element.DivNonzero.Assumptions,
    Element.Mul.circuit, Element.Mul.Assumptions
  ]
  obtain ⟨h_curve, h_order⟩ := h_assumptions
  -- Only non-trivial subcircuit goal: DivNonzero needs y+y ≠ 0
  have hy : input_y ≠ 0 := h_order ⟨input_x, input_y⟩ h_curve
  rw [← two_mul]; exact mul_ne_zero (NeZero.ne 2) hy

def circuit (curveParams : Spec.CurveParams p) : GeneralFormalCircuit (F p) Spec.Point Spec.Point :=
  {
    elaborated with
    Assumptions := Assumptions curveParams,
    Spec := Spec curveParams,
    soundness := soundness curveParams,
    completeness := completeness curveParams
  }

end Ragu.Circuits.Point.Double
