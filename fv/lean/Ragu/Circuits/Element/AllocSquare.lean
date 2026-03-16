import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

def main (idx : ℕ) (_input : Unit) : Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← Core.AllocMul.circuit idx default
  assertZero (x - y)
  return ⟨x, z⟩

def Assumptions (idx : ℕ) (_input : Unit) (data : ProverData (F p)) :=
  let w := Core.AllocMul.readRow data idx
  w.x = w.y ∧ w.x * w.y = w.z

def Spec (_input : Unit) (out : Square (F p)) (_data : ProverData (F p)) :=
  out.a_sq = out.a^2

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) unit Square where
  main := main idx
  localLength _ := 3

theorem soundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) Spec := by
  circuit_proof_start
  simp [Core.AllocMul.circuit, Core.AllocMul.Spec] at h_holds
  obtain ⟨c1, c2⟩ := h_holds
  rw [add_neg_eq_zero] at c2
  rw [←c2] at c1
  rw [←c1]
  ring

theorem completeness (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (Assumptions idx) := by
  sorry

def circuit (idx : ℕ) : GeneralFormalCircuit (F p) unit Square :=
  { elaborated idx with Assumptions := Assumptions idx, Spec, soundness := soundness idx, completeness := completeness idx }

end Ragu.Circuits.Element.AllocSquare
