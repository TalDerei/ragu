import Clean.Circuit
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Element.Square
variable {p : ℕ} [Fact p.Prime]

def main (x : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  return ←Mul.circuit ⟨x, x⟩

def Assumptions (_input : F p) := True

def Spec (input : F p) (out : F p) :=
  out = input^2

instance elaborated : ElaboratedCircuit (F p) field field main where
  output _ offset := varFromOffset field (offset + 2)
  localLength _ := 3

theorem soundness : Soundness (F p) (Input := field) (Output := field) main Assumptions Spec := by
  circuit_proof_start
  simp [circuit_norm, Mul.circuit, Mul.Assumptions, Mul.Spec] at h_holds ⊢
  rw [h_holds]
  ring

theorem completeness : Completeness (F p) (Input := field) (Output := field) main Assumptions := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions]

def circuit : FormalCircuit (F p) field field :=
  { main := main, elaborated := elaborated, Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Square
