import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct

-- quotient * denominator = numerator, with denominator = y, numerator = x
def main (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p)) (input : Var Inputs (F p))
    : Circuit (F p) (Var field (F p)) := do
  let ⟨quotient, denominator, numerator⟩ ← Core.AllocMul.circuit hintReader ()
  assertZero (input.x - numerator)
  assertZero (input.y - denominator)
  return quotient

def GeneralAssumptions (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    (input : Inputs (F p)) (_data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let r := hintReader hint
  r.y = input.y ∧ r.x * r.y = input.x ∧ (input.y ≠ 0 ∨ input.x = 0)

-- The disjunction `y ≠ 0 ∨ x ≠ 0` (rather than just `y ≠ 0`) reflects what the
-- circuit actually enforces via `quotient · y = x`:
--  * `y ≠ 0`: quotient is forced to `x / y`.
--  * `y = 0 ∧ x ≠ 0`: no valid witness exists; any prover transcript fails.
--  * `y = 0 ∧ x = 0`: quotient is unconstrained (premise is false, Spec is
--    vacuously true).
-- Callers of this gadget must establish `(x, y) ≠ (0, 0)` upstream or accept
-- the unconstrained-output carve-out. See `element.rs:273-280` for the
-- corresponding Rust `div_nonzero` doc comment.
def GeneralSpec (input : Inputs (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 ∨ input.x ≠ 0 → out = input.x / input.y

instance elaborated (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p)) :
    ElaboratedCircuit (F p) Inputs field where
  main := main hintReader
  localLength _ := 3

theorem generalSoundness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) GeneralSpec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec, GeneralSpec
  ]
  grind

theorem generalCompleteness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader) (GeneralAssumptions hintReader) := by
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

def generalCircuit (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) Inputs field :=
  { elaborated hintReader with
    Assumptions := GeneralAssumptions hintReader,
    Spec := GeneralSpec,
    soundness := generalSoundness hintReader,
    completeness := generalCompleteness hintReader }

end Ragu.Circuits.Element.DivNonzero
