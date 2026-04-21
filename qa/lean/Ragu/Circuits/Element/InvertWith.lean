import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.InvertWith
variable {p : ℕ} [Fact p.Prime]

/-- `invert_with` allocates a mul gate `(a, b, c)` with `a·b = c`, then
enforces `a = input` and `c = 1`, returning `b` as the inverse wire. -/
def main (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p)) (input : Expression (F p))
    : Circuit (F p) (Expression (F p)) := do
  let ⟨a, b, c⟩ ← Core.AllocMul.circuit hintReader ()
  assertZero (a - input)
  assertZero (c - 1)
  return b

def GeneralAssumptions (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    (input : F p) (_data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let r := hintReader hint
  r.x = input ∧ r.x * r.y = 1

def GeneralSpec (input : F p) (out : F p) (_data : ProverData (F p)) :=
  input * out = 1

instance elaborated (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : ElaboratedCircuit (F p) field field where
  main := main hintReader
  localLength _ := 3

theorem generalSoundness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) GeneralSpec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec
  ]
  obtain ⟨h_mul, h_a, h_c⟩ := h_holds
  rw [add_neg_eq_zero] at h_a h_c
  rw [h_a, h_c] at h_mul
  exact h_mul

theorem generalCompleteness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader) (GeneralAssumptions hintReader) := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.Spec, Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨_, h_x_eq, h_y_eq, h_z_eq⟩ := h_env
  simp only [GeneralAssumptions] at h_assumptions
  obtain ⟨h_x_in, h_prod_in⟩ := h_assumptions
  rw [add_neg_eq_zero, add_neg_eq_zero]
  refine ⟨?_, ?_⟩
  · rw [h_x_eq]; exact h_x_in
  · rw [h_z_eq]; exact h_prod_in

def generalCircuit (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) field field :=
  { elaborated hintReader with
    Assumptions := GeneralAssumptions hintReader,
    Spec := GeneralSpec,
    soundness := generalSoundness hintReader,
    completeness := generalCompleteness hintReader }

end Ragu.Circuits.Element.InvertWith
