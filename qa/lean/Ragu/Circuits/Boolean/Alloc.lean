import Clean.Circuit
import Clean.Gadgets.Boolean
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Boolean.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- `Boolean::alloc` constrains a wire to hold `0` or `1`.

Delegates the 3-wire `a * b = c` gate to `Core.AllocMul`, feeding it
the row `(v, 1 - v, 0)` derived from the boolean hint, then asserts
`c = 0` (collapsing the gate to `a * b = 0`) and `1 - a - b = 0`
(binding `b = 1 - a`). Together: `a * (1 - a) = 0`, so `a ∈ {0, 1}`. -/
def main (hintReader : ProverHint (F p) → Bool) (_input : Unit)
    : Circuit (F p) (Var field (F p)) := do
  let ⟨a, b, c⟩ ← Core.AllocMul.circuit
    (fun hint =>
      let v : F p := if hintReader hint then 1 else 0
      ⟨v, 1 - v, 0⟩) ()
  assertZero c
  assertZero (1 - a - b)
  return a

def Assumptions (_hintReader : ProverHint (F p) → Bool)
    (_input : Unit) (_data : ProverData (F p)) (_hint : ProverHint (F p)) := True

/-- The verifier learns the output wire is boolean-valued. -/
def Spec (_input : Unit) (out : F p) (_data : ProverData (F p)) :=
  IsBool out

instance elaborated (hintReader : ProverHint (F p) → Bool)
    : ElaboratedCircuit (F p) unit field where
  main := main hintReader
  localLength _ := 3

theorem soundness (hintReader : ProverHint (F p) → Bool)
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) Spec := by
  circuit_proof_start [Core.AllocMul.circuit, Core.AllocMul.Spec]
  obtain ⟨h_mul, h_c, h_lin⟩ := h_holds
  -- h_mul : a * b = c, h_c : c = 0, h_lin : 1 - a - b = 0
  rw [h_c] at h_mul
  rcases mul_eq_zero.mp h_mul with ha | hb
  · exact Or.inl ha
  · exact Or.inr (by linear_combination -h_lin - hb)

theorem completeness (hintReader : ProverHint (F p) → Bool)
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader) (Assumptions hintReader) := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨_, hx, hy, hz⟩ := h_env
  -- hx : a = v, hy : b = 1 - v, hz : c = v * (1 - v), where v ∈ {0, 1}.
  refine ⟨?_, ?_⟩
  · rw [hz]; by_cases h : hintReader env.hint <;> simp [h]
  · rw [hx, hy]; ring

def circuit (hintReader : ProverHint (F p) → Bool)
    : GeneralFormalCircuit (F p) unit field :=
  { elaborated hintReader with
    Assumptions := Assumptions hintReader,
    Spec := Spec,
    soundness := soundness hintReader,
    completeness := completeness hintReader }

end Ragu.Circuits.Boolean.Alloc
