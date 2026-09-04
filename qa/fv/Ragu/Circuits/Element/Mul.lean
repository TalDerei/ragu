import Clean.Circuit
import Ragu.Circuits.Core.Mul

namespace Ragu.Circuits.Element.Mul
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (input : Var Input (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨x, y, z⟩ ← Core.mul fun env =>
    ⟨env input.x, env input.y, env input.x * env input.y⟩
  assertZero (x - input.x)
  assertZero (y - input.y)
  return z

def Assumptions (_input : Input (F p)) := True

def Spec (input : Input (F p)) (out : field (F p)) :=
  out = input.x * input.y

instance elaborated : ElaboratedCircuit (F p) Input field main where
  output _ offset := varFromOffset field (offset + 2)
  localLength _ := 3

theorem soundness : Soundness (F p) (Input := Input) (Output := field) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [sub_eq_zero] at c2 c3
  rw [←c2, ←c3, c1]

theorem completeness : Completeness (F p) (Input := Input) (Output := field) main Assumptions := by
  circuit_proof_start
  grind

def circuit : FormalCircuit (F p) Input field :=
  { main := main, elaborated := elaborated, Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Mul
