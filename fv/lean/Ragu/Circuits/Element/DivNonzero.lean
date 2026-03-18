import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct

-- quotient * denominator = numerator, with denominator = y, numerator = x
def main (idx : ℕ) (input : Var Inputs (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨quotient, denominator, numerator⟩ ← Core.AllocMul.circuit idx ()
  assertZero (input.x - numerator)
  assertZero (input.y - denominator)
  return quotient

def GeneralAssumptions (idx : ℕ) (input : Inputs (F p)) (data : ProverData (F p)) :=
  let row := Core.AllocMul.readRow data idx
  row.y = input.y ∧ row.z = input.x ∧ (input.y ≠ 0 ∨ input.x = 0)

def GeneralSpec (input : Inputs (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 → out = input.x / input.y

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) Inputs field where
  main := main idx
  localLength _ := 3

theorem generalSoundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) GeneralSpec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec
  ]
  obtain ⟨h_mul, h_x, h_y⟩ := h_holds
  rw [add_neg_eq_zero] at h_x h_y
  intro h_y_ne
  rw [←h_x, ←h_y] at h_mul
  exact eq_div_of_mul_eq h_y_ne h_mul

theorem generalCompleteness (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (GeneralAssumptions idx) := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.Spec, Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨_, h_eq⟩ := h_env
  simp only [GeneralAssumptions] at h_assumptions
  obtain ⟨h_y_eq, h_z_eq, _⟩ := h_assumptions
  have h_eq_z := congr_arg Core.AllocMul.Row.z h_eq
  have h_eq_y := congr_arg Core.AllocMul.Row.y h_eq
  simp only [] at h_eq_z h_eq_y h_y_eq h_z_eq
  rw [add_neg_eq_zero, add_neg_eq_zero]
  exact ⟨by rw [h_eq_z, h_z_eq], by rw [h_eq_y, h_y_eq]⟩

def generalCircuit (idx : ℕ) : GeneralFormalCircuit (F p) Inputs field :=
  { elaborated idx with
    Assumptions := GeneralAssumptions idx,
    Spec := GeneralSpec,
    soundness := generalSoundness idx,
    completeness := generalCompleteness idx }

end Ragu.Circuits.Element.DivNonzero
