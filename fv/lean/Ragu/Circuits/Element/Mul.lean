import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.Mul
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (idx : ℕ) (input : Var Input (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨x, y, z⟩ ← Core.AllocMul.circuit idx default
  assertZero (x - input.x)
  assertZero (y - input.y)
  return z

def Assumptions (idx : ℕ) (input : Input (F p)) (data : ProverData (F p)) :=
  let w := Core.AllocMul.readRow data idx
  w.x = input.x ∧ w.y = input.y ∧ w.x * w.y = w.z

def Spec (input : Input (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  out = input.x * input.y

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) Input field where
  main := main idx
  localLength _ := 3

theorem soundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) Spec := by
  circuit_proof_start
  simp [Core.AllocMul.circuit, Core.AllocMul.Spec] at h_holds
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c2 c3
  rw [←c2, ←c3, c1]

theorem completeness (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (Assumptions idx) := by
  sorry

def circuit (idx : ℕ) : GeneralFormalCircuit (F p) Input field :=
  {
    elaborated idx with
    Assumptions := Assumptions idx,
    Spec,
    soundness := soundness idx,
    completeness := completeness idx
  }

end Ragu.Circuits.Element.Mul
