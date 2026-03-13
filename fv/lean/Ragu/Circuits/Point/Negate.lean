import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Element.DivNonzero
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Negate
variable {p : ℕ} [Fact p.Prime]

def main (input : Var Spec.Point (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x, y⟩ := input
  return ⟨x, -y⟩

def Assumptions (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) :=
  input.isOnCurve curveParams

def Spec (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) (output : Spec.Point (F p)) :=
  output = Spec.Point.negate input ∧ output.isOnCurve curveParams

instance elaborated : ElaboratedCircuit (F p) Spec.Point Spec.Point where
  main
  localLength _ := 0

theorem soundness (curveParams : Spec.CurveParams p) : Soundness (F p) elaborated (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start
  simp_all only [Spec.Point.isOnCurve, id_eq, Spec.Point.negate, even_two, Even.neg_pow, and_self]


theorem completeness (curveParams : Spec.CurveParams p) : Completeness (F p) elaborated (Assumptions curveParams) := by
  sorry

def circuit (curveParams : Spec.CurveParams p) : FormalCircuit (F p) Spec.Point Spec.Point :=
  {
    elaborated with
    Assumptions := Assumptions curveParams,
    Spec := Spec curveParams,
    soundness := soundness curveParams,
    completeness := completeness curveParams
  }

end Ragu.Circuits.Point.Negate
