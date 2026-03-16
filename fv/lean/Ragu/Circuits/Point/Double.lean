import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Element.DivNonzero
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Double
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : F p)]

-- 4 AllocMul instances: idx..idx+3
-- idx+0: Square(x) → x²
-- idx+1: DivNonzero(3x², 2y) → delta
-- idx+2: Square(delta) → delta²
-- idx+3: Mul(delta, x-x3) → delta*(x-x3)
def main (idx : ℕ) (input : Var Spec.Point (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x, y⟩ := input

  -- delta = 3x^2 / 2y
  let double_y := y + y
  let ⟨x2⟩ ← Element.Square.circuit idx ⟨x⟩
  let x2_scaled := (3 : F p) * x2
  let delta ← Element.DivNonzero.circuit (idx + 1) ⟨x2_scaled, double_y⟩

  -- x3 = delta^2 - 2x
  let double_x := x + x
  let ⟨delta2⟩ ← Element.Square.circuit (idx + 2) ⟨delta⟩
  let x3 := delta2 - double_x

  -- y3 = delta * (x - x3) - y
  let x_sub_x3 := x - x3
  let delta_x_sub_3 ← Element.Mul.circuit (idx + 3) ⟨delta, x_sub_x3⟩
  let y3 := delta_x_sub_3 - y

  return ⟨x3, y3⟩

def Assumptions (curveParams : Spec.CurveParams p) (idx : ℕ) (input : Spec.Point (F p)) (data : ProverData (F p)) :=
  input.isOnCurve curveParams ∧
  -- for the circuit to be sound, there must not exist points of order 2 on the curve,
  -- therefore soundness is also conditioned on the following property:
  curveParams.noOrderTwoPoints ∧
  -- witness validity for each subcircuit
  Element.Square.Assumptions idx ⟨input.x⟩ data ∧
  Element.DivNonzero.Assumptions (idx + 1) ⟨3 * (Core.AllocMul.readRow data idx).z, input.y + input.y⟩ data ∧
  Element.Square.Assumptions (idx + 2) ⟨(Core.AllocMul.readRow data (idx + 1)).x⟩ data ∧
  Element.Mul.Assumptions (idx + 3) ⟨(Core.AllocMul.readRow data (idx + 1)).x,
    input.x - ((Core.AllocMul.readRow data (idx + 2)).z - (input.x + input.x))⟩ data

-- Spec is conditional on curve membership and no order-2 points
def Spec (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) (output : Spec.Point (F p)) (_data : ProverData (F p)) :=
  input.isOnCurve curveParams →
  curveParams.noOrderTwoPoints →
  (match input.double with
  | none => False -- this case never happens
  | some double => output = double)
  ∧
  output.isOnCurve curveParams

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) Spec.Point Spec.Point where
  main := main idx
  localLength _ := 12

theorem soundness (curveParams : Spec.CurveParams p) (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) (Spec curveParams) := by
  circuit_proof_start
  simp [circuit_norm,
    Element.Square.circuit, Element.Square.Spec,
    Element.DivNonzero.circuit, Element.DivNonzero.Spec,
    Element.Mul.circuit, Element.Mul.Spec
  ] at h_holds ⊢

  obtain ⟨c1, c2, c3, c4⟩ := h_holds

  intro h_membership h_order
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


theorem completeness (curveParams : Spec.CurveParams p) (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (Assumptions curveParams idx) := by
  sorry

def circuit (curveParams : Spec.CurveParams p) (idx : ℕ) : GeneralFormalCircuit (F p) Spec.Point Spec.Point :=
  {
    elaborated idx with
    Assumptions := Assumptions curveParams idx,
    Spec := Spec curveParams,
    soundness := soundness curveParams idx,
    completeness := completeness curveParams idx
  }

end Ragu.Circuits.Point.Double
