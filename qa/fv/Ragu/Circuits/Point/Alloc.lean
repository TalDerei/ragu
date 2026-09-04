import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Alloc
variable {p : ℕ} [Fact p.Prime]

def main (curveParams : Spec.CurveParams p)
    (input : Var (UnconstrainedDepNative Spec.Point) (F p)) :
    Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨x, x_sq⟩ ← Element.AllocSquare.circuit fun env => (input env).x
  let x3 ← Element.Mul.circuit ⟨x, x_sq⟩
  let ⟨y, y_sq⟩ ← Element.AllocSquare.circuit fun env => (input env).y
  assertZero ((x3 + (curveParams.b * 1)) - y_sq)
  return ⟨x, y⟩

def Assumptions (_input : Unit) (_data : ProverData (F p)) := True

def ProverAssumptions (curveParams : Spec.CurveParams p)
    (input : Spec.Point (F p)) (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  input.isOnCurve curveParams

def Spec (curveParams : Spec.CurveParams p) (_input : Unit) (out : Spec.Point (F p)) (_data : ProverData (F p)) :=
  out.isOnCurve curveParams

def ProverSpec (input : Spec.Point (F p))
    (out : Spec.Point (F p)) (_hint : ProverHint (F p)) :=
  out = input

instance elaborated (curveParams : Spec.CurveParams p) :
    ElaboratedCircuit (F p) (UnconstrainedDepNative Spec.Point) Spec.Point (main curveParams) where
  localLength _ := 9

theorem soundness (curveParams : Spec.CurveParams p) :
    GeneralFormalCircuit.WithHint.Soundness (F p) (Input := (UnconstrainedDepNative Spec.Point)) (Output := Spec.Point) (main curveParams)
      Assumptions (Spec curveParams) := by
  circuit_proof_start [
    Element.AllocSquare.circuit, Element.AllocSquare.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  simp only [Spec.Point.isOnCurve]
  obtain ⟨h_sq_x, h_mul, h_sq_y, h_assert⟩ := h_holds
  rw [sub_eq_zero, mul_one] at h_assert
  rw [← h_sq_y, ← h_assert, h_mul, h_sq_x]
  ring

theorem completeness (curveParams : Spec.CurveParams p)
    : GeneralFormalCircuit.WithHint.Completeness (F p) (Input := (UnconstrainedDepNative Spec.Point)) (Output := Spec.Point) (main curveParams)
      (ProverAssumptions curveParams) ProverSpec := by
  circuit_proof_start [
    Element.AllocSquare.circuit,
    Element.AllocSquare.Spec,
    Element.AllocSquare.ProverSpec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ]
  obtain ⟨⟨_, h_x, h_xsq⟩, h_mul, ⟨_, h_y, h_ysq⟩⟩ := h_env
  constructor
  · rw [h_mul, h_x, h_xsq, h_ysq, mul_one, sub_eq_zero]
    rw [show input.x * input.x ^ 2 = input.x ^ 3 from by ring]
    rw [← h_assumptions]
  · cases input
    simp_all

def circuit (curveParams : Spec.CurveParams p) :
    GeneralFormalCircuit.WithHint (F p) (UnconstrainedDepNative Spec.Point) Spec.Point where
  main := main curveParams
  elaborated := elaborated curveParams
  Assumptions := Assumptions
  Spec := Spec curveParams
  ProverAssumptions := ProverAssumptions curveParams
  ProverSpec := ProverSpec
  soundness := soundness curveParams
  completeness := completeness curveParams

end Ragu.Circuits.Point.Alloc
