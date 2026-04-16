import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Alloc
variable {p : ℕ} [Fact p.Prime]

def main (curveParams : Spec.CurveParams p)
    (hintX hintY : ProverData (F p) → F p) (_input : Unit) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x, x_sq⟩ ← Element.AllocSquare.generalCircuit hintX ()
  let x3 ← Element.Mul.circuit ⟨x, x_sq⟩
  let ⟨y, y_sq⟩ ← Element.AllocSquare.generalCircuit hintY ()
  assertZero ((x3 + (curveParams.b * 1)) - y_sq)
  return ⟨x, y⟩

def Assumptions (curveParams : Spec.CurveParams p)
    (hintX hintY : ProverData (F p) → F p) (_input : Unit) (data : ProverData (F p)) :=
  (hintX data)^3 + curveParams.b = (hintY data)^2

def Spec (curveParams : Spec.CurveParams p) (_input : Unit) (out : Spec.Point (F p)) (_data : ProverData (F p)) :=
  out.isOnCurve curveParams

instance elaborated (curveParams : Spec.CurveParams p)
    (hintX hintY : ProverData (F p) → F p) : ElaboratedCircuit (F p) unit Spec.Point where
  main := main curveParams hintX hintY
  localLength _ := 9

theorem soundness (curveParams : Spec.CurveParams p)
    (hintX hintY : ProverData (F p) → F p) :
    GeneralFormalCircuit.Soundness (F p) (elaborated curveParams hintX hintY) (Spec curveParams) := by
  circuit_proof_start [
    Element.AllocSquare.generalCircuit, Element.AllocSquare.Assumptions,
    Element.AllocSquare.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  simp only [Spec.Point.isOnCurve]
  obtain ⟨h_sq_x, h_mul, h_sq_y, h_assert⟩ := h_holds
  rw [add_neg_eq_zero, mul_one] at h_assert
  rw [← h_sq_y, ← h_assert, h_mul, h_sq_x]
  ring

theorem completeness (curveParams : Spec.CurveParams p)
    (hintX hintY : ProverData (F p) → F p) :
    GeneralFormalCircuit.Completeness (F p) (elaborated curveParams hintX hintY)
      (Assumptions curveParams hintX hintY) := by
  circuit_proof_start [
    Element.AllocSquare.generalCircuit, Element.AllocSquare.Assumptions,
    Element.AllocSquare.Spec, Element.AllocSquare.CompletenessSpec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  obtain ⟨⟨_, h_x, h_xsq⟩, h_mul, ⟨_, _, h_ysq⟩⟩ := h_env
  rw [h_mul, h_x, h_xsq, h_ysq, mul_one, add_neg_eq_zero]
  rw [show hintX env.data * hintX env.data ^ 2 = hintX env.data ^ 3 from by ring]
  exact h_assumptions

def circuit (curveParams : Spec.CurveParams p)
    (hintX hintY : ProverData (F p) → F p) : GeneralFormalCircuit (F p) unit Spec.Point :=
  {
    (elaborated curveParams hintX hintY) with
    Assumptions := Assumptions curveParams hintX hintY,
    Spec := (Spec curveParams),
    soundness := soundness curveParams hintX hintY,
    completeness := completeness curveParams hintX hintY
  }

end Ragu.Circuits.Point.Alloc
