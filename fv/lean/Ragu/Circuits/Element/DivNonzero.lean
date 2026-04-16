import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct

-- quotient * denominator = numerator, with denominator = y, numerator = x
def main (hint : ProverData (F p) → Core.AllocMul.Row (F p)) (input : Var Inputs (F p))
    : Circuit (F p) (Var field (F p)) := do
  let ⟨quotient, denominator, numerator⟩ ← Core.AllocMul.circuit hint ()
  assertZero (input.x - numerator)
  assertZero (input.y - denominator)
  return quotient

def GeneralAssumptions (hint : ProverData (F p) → Core.AllocMul.Row (F p))
    (input : Inputs (F p)) (data : ProverData (F p)) :=
  let r := hint data
  r.y = input.y ∧ r.x * r.y = input.x ∧ (input.y ≠ 0 ∨ input.x = 0)

def GeneralSpec (input : Inputs (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 → out = input.x / input.y

instance elaborated (hint : ProverData (F p) → Core.AllocMul.Row (F p))
    : ElaboratedCircuit (F p) Inputs field where
  main := main hint
  localLength _ := 3

theorem generalSoundness (hint : ProverData (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hint) GeneralSpec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec
  ]
  obtain ⟨h_mul, h_x, h_y⟩ := h_holds
  rw [add_neg_eq_zero] at h_x h_y
  intro h_y_ne
  rw [←h_x, ←h_y] at h_mul
  exact eq_div_of_mul_eq h_y_ne h_mul

theorem generalCompleteness (hint : ProverData (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hint) (GeneralAssumptions hint) := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.Spec, Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨_, h_x_eq, h_y_eq, h_z_eq⟩ := h_env
  simp only [GeneralAssumptions] at h_assumptions
  obtain ⟨h_y_in, h_z_in, _⟩ := h_assumptions
  rw [add_neg_eq_zero, add_neg_eq_zero]
  refine ⟨?_, ?_⟩
  · rw [h_z_eq]; exact h_z_in.symm
  · rw [h_y_eq]; exact h_y_in.symm

def generalCircuit (hint : ProverData (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) Inputs field :=
  { elaborated hint with
    Assumptions := GeneralAssumptions hint,
    Spec := GeneralSpec,
    soundness := generalSoundness hint,
    completeness := generalCompleteness hint }

end Ragu.Circuits.Element.DivNonzero
