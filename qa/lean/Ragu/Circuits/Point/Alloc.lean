import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- Alloc reads two field elements from the hint — one for the x-coordinate,
    one for y. Callers supply the two readers. -/
def main (curveParams : Spec.CurveParams p)
    (xReader yReader : ProverHint (F p) → F p)
    (_input : Unit) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x, x_sq⟩ ← Element.AllocSquare.generalCircuit xReader ()
  let x3 ← Element.Mul.circuit ⟨x, x_sq⟩
  let ⟨y, y_sq⟩ ← Element.AllocSquare.generalCircuit yReader ()
  assertZero ((x3 + (curveParams.b * 1)) - y_sq)
  return ⟨x, y⟩

def Assumptions (curveParams : Spec.CurveParams p)
    (xReader yReader : ProverHint (F p) → F p)
    (_input : Unit) (_data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let hx := xReader hint
  let hy := yReader hint
  hx ^ 3 + curveParams.b = hy ^ 2

def Spec (curveParams : Spec.CurveParams p) (_input : Unit) (out : Spec.Point (F p)) (_data : ProverData (F p)) :=
  out.isOnCurve curveParams

instance elaborated (curveParams : Spec.CurveParams p)
    (xReader yReader : ProverHint (F p) → F p) :
    ElaboratedCircuit (F p) unit Spec.Point where
  main := main curveParams xReader yReader
  localLength _ := 9

theorem soundness (curveParams : Spec.CurveParams p)
    (xReader yReader : ProverHint (F p) → F p) :
    GeneralFormalCircuit.Soundness (F p) (elaborated curveParams xReader yReader) (Spec curveParams) := by
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
    (xReader yReader : ProverHint (F p) → F p) :
    GeneralFormalCircuit.Completeness (F p) (elaborated curveParams xReader yReader)
      (Assumptions curveParams xReader yReader) := by
  circuit_proof_start [
    Element.AllocSquare.generalCircuit, Element.AllocSquare.Assumptions,
    Element.AllocSquare.Spec, Element.AllocSquare.CompletenessSpec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  obtain ⟨⟨_, h_x, h_xsq⟩, h_mul, ⟨_, _, h_ysq⟩⟩ := h_env
  rw [h_mul, h_x, h_xsq, h_ysq, mul_one, add_neg_eq_zero]
  set hx := xReader env.hint
  set hy := yReader env.hint
  rw [show hx * hx ^ 2 = hx ^ 3 from by ring]
  exact h_assumptions

def circuit (curveParams : Spec.CurveParams p)
    (xReader yReader : ProverHint (F p) → F p) :
    GeneralFormalCircuit (F p) unit Spec.Point :=
  {
    (elaborated curveParams xReader yReader) with
    Assumptions := Assumptions curveParams xReader yReader,
    Spec := (Spec curveParams),
    soundness := soundness curveParams xReader yReader,
    completeness := completeness curveParams xReader yReader
  }

end Ragu.Circuits.Point.Alloc
