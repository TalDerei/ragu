import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.Mul
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (input : Var Input (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨x, y, z⟩ ← subcircuit Ragu.Circuits.Core.AllocMul.circuit default
  assertZero (x - input.x)
  assertZero (y - input.y)
  return z

def Assumptions (_input : Input (F p)) := True

def Spec (input : Input (F p)) (out : field (F p)) :=
  out = input.x * input.y

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp [Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec] at h_holds
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c2 c3
  rw [←c2, ←c3, c1]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Mul
