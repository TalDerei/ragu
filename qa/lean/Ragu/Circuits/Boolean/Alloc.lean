import Clean.Circuit
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Boolean.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- `Boolean::alloc` constrains a wire to hold `0` or `1`.

Emits the same 3-wire gate as `Core.AllocMul` (constraint `a * b = c`),
then asserts `c = 0` (collapsing the gate to `a * b = 0`) and
`1 - a - b = 0` (binding `b = 1 - a`). Together: `a * (1 - a) = 0`, so
`a ∈ {0, 1}`. Flat reimplementation to keep `same_constraints` tractable. -/
def main (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p)) (_ : Unit)
    : Circuit (F p) (Expression (F p)) := do
  let ⟨a, b, c⟩ ← (witness fun env =>
    let r := hintReader env.hint
    (⟨r.x, r.y, r.x * r.y⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (a * b - c)
  assertZero c
  assertZero (1 - a - b)
  return a

/-- For completeness, the hint must describe a valid boolean row:
`r.x + r.y = 1` (so the linear constraint holds) and `r.x * r.y = 0`
(so the gate constraint reduces to `c = 0`). Over a field these
together force `r.x, r.y ∈ {0, 1}`. -/
def GeneralAssumptions (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    (_input : Unit) (_data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let r := hintReader hint
  r.x + r.y = 1 ∧ r.x * r.y = 0

/-- The verifier learns the output wire is boolean-valued. -/
def GeneralSpec (_input : Unit) (out : F p) (_data : ProverData (F p)) :=
  out = 0 ∨ out = 1

instance elaborated (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : ElaboratedCircuit (F p) unit field where
  main := main hintReader
  localLength _ := 3

theorem generalSoundness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) GeneralSpec := by
  circuit_proof_start
  obtain ⟨h_mul, h_c, h_lin⟩ := h_holds
  -- h_mul : a * b - c = 0, h_c : c = 0, h_lin : 1 - a - b = 0
  rw [add_neg_eq_zero] at h_mul
  rw [h_c] at h_mul
  rcases mul_eq_zero.mp h_mul with ha | hb
  · exact Or.inl ha
  · exact Or.inr (by linear_combination -h_lin - hb)

theorem generalCompleteness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader) (GeneralAssumptions hintReader) := by
  circuit_proof_start
  simp only [GeneralAssumptions] at h_assumptions
  obtain ⟨h_sum, h_prod⟩ := h_assumptions
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [show i₀ + 1 + 1 = i₀ + 2 from by omega, h0, h1, h2]; ring
  · rw [show i₀ + 1 + 1 = i₀ + 2 from by omega, h2]; exact h_prod
  · rw [h0, h1]; linear_combination -h_sum

def generalCircuit (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) unit field :=
  { elaborated hintReader with
    Assumptions := GeneralAssumptions hintReader,
    Spec := GeneralSpec,
    soundness := generalSoundness hintReader,
    completeness := generalCompleteness hintReader }

end Ragu.Circuits.Boolean.Alloc
