import Clean.Circuit
import Ragu.Circuits.Element.IsZero

namespace Ragu.Circuits.Element.IsEqual
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  a : F
  b : F
deriving ProvableStruct

/-- `Element::is_equal(other)` is `self.sub(other).is_zero()` in Rust. The
Lean reimpl mirrors that delegation directly: `IsZero` applied to the
virtual difference `a - b`. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  return ←IsZero.circuit (input.a - input.b)

def Assumptions (_input : Input (F p)) := True

/-- The output equals `1` when the two inputs are equal and `0` otherwise. -/
def Spec (input : Input (F p)) (out : F p) :=
  out = if input.a = input.b then 1 else 0

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 6

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp [circuit_norm, IsZero.circuit, IsZero.Assumptions, IsZero.Spec] at h_holds ⊢
  simp only [add_neg_eq_zero] at h_holds
  exact h_holds

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [IsZero.circuit, IsZero.Assumptions]

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.IsEqual
