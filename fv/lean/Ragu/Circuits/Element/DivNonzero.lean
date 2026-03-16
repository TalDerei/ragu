import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct

-- w maps as: (quotient, denominator, numerator) i.e. quotient * denominator = numerator
def main (idx : ℕ) (input : Var Inputs (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨quotient, denominator, numerator⟩ ← Core.AllocMul.circuit idx default

  assertZero (input.x - numerator)
  assertZero (input.y - denominator)

  return quotient

def Assumptions (idx : ℕ) (input : Inputs (F p)) (data : ProverData (F p)) :=
  let w := Core.AllocMul.readRow data idx
  input.y ≠ 0 ∧ w.y = input.y ∧ w.z = input.x ∧ w.x * w.y = w.z

-- Spec is conditional: soundness does not use assumptions
def Spec (input : Inputs (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 → out = input.x / input.y

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) Inputs field where
  main := main idx
  localLength _ := 3

theorem soundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) Spec := by
  circuit_proof_start
  simp [circuit_norm, Core.AllocMul.circuit, Core.AllocMul.Spec] at h_holds ⊢
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c2 c3
  rw [←c2, ←c3] at c1
  intro h
  apply eq_div_of_mul_eq <;> assumption

theorem completeness (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (Assumptions idx) := by
  sorry

def circuit (idx : ℕ) : GeneralFormalCircuit (F p) Inputs field :=
  {
    elaborated idx with
    Assumptions := Assumptions idx,
    Spec,
    soundness := soundness idx,
    completeness := completeness idx
  }

end Ragu.Circuits.Element.DivNonzero
