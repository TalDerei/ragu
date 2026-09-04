import Clean.Circuit
import Clean.Gadgets.Boolean
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

/-- Caller must promise `cond` is boolean; the high-level "conditional
negate" description below requires this to hold. -/
def Assumptions (input : Input (F p)) :=
  IsBool input.cond

/-- High-level operation: when `cond = 1`, negate `y`; else leave `y`
unchanged. `x` is always unchanged. -/
def Spec (input : Input (F p)) (output : Spec.Point (F p)) :=
  output.x = input.x ∧
  output.y = if input.cond = 1 then -input.y else input.y

instance elaborated : ElaboratedCircuit (F p) Input Spec.Point main where
  localLength _ := 3
  -- `y` selected against `-y`: the `ConditionalSelect` output is `y + (its Mul wire)`.
  output input offset := ⟨input.x, input.y + varFromOffset field (offset + 2)⟩
  output_eq := by
    simp [main, circuit_norm, Boolean.ConditionalSelect.circuit]

theorem soundness : Soundness (F p) (Input := Input) (Output := Spec.Point) main Assumptions Spec := by
  circuit_proof_start [Boolean.ConditionalSelect.circuit,
    Boolean.ConditionalSelect.Assumptions, Boolean.ConditionalSelect.Spec]
  exact h_holds h_assumptions

theorem completeness : Completeness (F p) (Input := Input) (Output := Spec.Point) main Assumptions := by
  circuit_proof_start [Boolean.ConditionalSelect.circuit,
    Boolean.ConditionalSelect.Assumptions]
  exact h_assumptions

def circuit : FormalCircuit (F p) Input Spec.Point :=
  { main := main, elaborated := elaborated, Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Point.ConditionalNegate
