import Clean.Circuit
import Ragu.Circuits.Boolean.ConditionalSelect
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.ConditionalEndo
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  cond : F
  x : F
  y : F
deriving ProvableStruct

/-- `Point::conditional_endo(cond)` is `(cond.conditional_select(self.x,
self.x.scale(ζ)), self.y)` in Rust. The Lean reimpl mirrors that
delegation directly: `ConditionalSelect` between `x` and `ζ·x`, with `y`
unchanged. -/
def main (curveParams : Spec.CurveParams p) (input : Var Input (F p))
    : Circuit (F p) (Var Spec.Point (F p)) := do
  let new_x ← Boolean.ConditionalSelect.circuit
    ⟨input.cond, input.x, curveParams.ζ * input.x⟩
  return ⟨new_x, input.y⟩

/-- Caller must promise `cond ∈ {0, 1}`; `Spec` holds unconditionally,
but is only meaningful as a "conditional endomorphism" under this
precondition. -/
def Assumptions (_curveParams : Spec.CurveParams p) (input : Input (F p)) :=
  input.cond = 0 ∨ input.cond = 1

/-- New x is `x + cond · (ζ·x - x)`; new y is unchanged. Under `cond = 0`
the x is unchanged; under `cond = 1` the x becomes `ζ·x`. -/
def Spec (curveParams : Spec.CurveParams p) (input : Input (F p))
    (output : Spec.Point (F p)) :=
  output.x = input.x + input.cond * (curveParams.ζ * input.x - input.x) ∧
  output.y = input.y

instance elaborated (curveParams : Spec.CurveParams p)
    : ElaboratedCircuit (F p) Input Spec.Point where
  main := main curveParams
  localLength _ := 3

theorem soundness (curveParams : Spec.CurveParams p)
    : Soundness (F p) (elaborated curveParams) (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start
  simp [circuit_norm, Boolean.ConditionalSelect.circuit,
    Boolean.ConditionalSelect.Assumptions, Boolean.ConditionalSelect.Spec] at h_holds
  exact h_holds h_assumptions

theorem completeness (curveParams : Spec.CurveParams p)
    : Completeness (F p) (elaborated curveParams) (Assumptions curveParams) := by
  circuit_proof_start [Boolean.ConditionalSelect.circuit,
    Boolean.ConditionalSelect.Assumptions]
  exact h_assumptions

def circuit (curveParams : Spec.CurveParams p) : FormalCircuit (F p) Input Spec.Point :=
  { elaborated curveParams with
    Assumptions := Assumptions curveParams,
    Spec := Spec curveParams,
    soundness := soundness curveParams,
    completeness := completeness curveParams }

end Ragu.Circuits.Point.ConditionalEndo
