import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Element.DivNonzero
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Endo
variable {p : ℕ} [Fact p.Prime]

def main (curveParams : Spec.CurveParams p) (input : Var Spec.Point (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x, y⟩ := input
  return ⟨curveParams.ζ * x, y⟩

def Assumptions (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) :=
  input.isOnCurve curveParams

def Spec (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) (output : Spec.Point (F p)) :=
  output = Spec.Point.endo input curveParams ∧
  output.isOnCurve curveParams

instance elaborated (curveParams : Spec.CurveParams p) : ElaboratedCircuit (F p) Spec.Point Spec.Point where
  main:= main curveParams
  localLength _ := 0

theorem soundness (curveParams : Spec.CurveParams p) : Soundness (F p) (elaborated curveParams) (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start
  simp [Spec.Point.isOnCurve, Spec.Point.endo] at h_holds ⊢
  ring_nf
  simp only [curveParams.h_small_order, one_mul]
  exact h_assumptions

theorem completeness (curveParams : Spec.CurveParams p) : Completeness (F p) (elaborated curveParams) (Assumptions curveParams) := by
  circuit_proof_start

def circuit (curveParams : Spec.CurveParams p) : FormalCircuit (F p) Spec.Point Spec.Point :=
  {
    elaborated curveParams with
    Assumptions := Assumptions curveParams,
    Spec := Spec curveParams,
    soundness := soundness curveParams,
    completeness := completeness curveParams
  }

end Ragu.Circuits.Point.Endo
