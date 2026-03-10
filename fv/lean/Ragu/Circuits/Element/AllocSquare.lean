import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

def main (_input : Unit) : Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← subcircuit Ragu.Circuits.Core.AllocMul.circuit default
  assertZero (x - y)
  return ⟨x, z⟩

def Assumptions (_input : Unit) := True

def Spec (_input : Unit) (out : Square (F p)) :=
  out.a_sq = out.a^2

instance elaborated : ElaboratedCircuit (F p) unit Square where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp [Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec] at h_holds
  obtain ⟨c1, c2⟩ := h_holds
  rw [add_neg_eq_zero] at c2
  rw [←c2] at c1
  rw [←c1]
  ring

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) unit Square :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.AllocSquare
