import Clean.Circuit
import Ragu.Circuits.Boolean.ConditionalSelect
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.ConditionalNegate
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  cond : F
  x : F
  y : F
deriving ProvableStruct

/-- `Point::conditional_negate(cond)` is `(self.x, cond.conditional_select(
self.y, self.y.negate()))` in Rust. The Lean reimpl mirrors that
delegation directly: `ConditionalSelect` between `y` and `-y`, with `x`
unchanged. -/
def main (input : Var Input (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let new_y ← Boolean.ConditionalSelect.circuit ⟨input.cond, input.y, -input.y⟩
  return ⟨input.x, new_y⟩

/-- Caller must promise `cond ∈ {0, 1}`; `Spec` holds unconditionally,
but is only meaningful as a "conditional negate" under this precondition. -/
def Assumptions (input : Input (F p)) :=
  input.cond = 0 ∨ input.cond = 1

/-- New y is `y + cond · (-y - y)`; new x is unchanged. Under `cond = 0`
the y is unchanged; under `cond = 1` the y becomes `-y`. -/
def Spec (input : Input (F p)) (output : Spec.Point (F p)) :=
  output.x = input.x ∧
  output.y = input.y + input.cond * (-input.y - input.y)

instance elaborated : ElaboratedCircuit (F p) Input Spec.Point where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp [circuit_norm, Boolean.ConditionalSelect.circuit,
    Boolean.ConditionalSelect.Assumptions, Boolean.ConditionalSelect.Spec] at h_holds
  exact h_holds h_assumptions

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [Boolean.ConditionalSelect.circuit,
    Boolean.ConditionalSelect.Assumptions]
  exact h_assumptions

def circuit : FormalCircuit (F p) Input Spec.Point :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Point.ConditionalNegate
