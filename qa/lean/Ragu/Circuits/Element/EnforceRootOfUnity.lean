import Clean.Circuit
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Element.EnforceRootOfUnity
variable {p : ℕ} [Fact p.Prime]

/-- `Element::enforce_root_of_unity(k)` enforces `self^(2^k) = 1` by
squaring `k` times. This extraction instance fixes k = 2 (enforces
`self^4 = 1`). Other values of k require analogous instances with the
appropriate number of square subcircuits.

Uses `GeneralFormalCircuit` directly (not `FormalCircuit` wrapped via
`isGeneralFormalCircuit`) because for this gadget `Assumptions = Spec`,
and the wrapper would collapse `Spec` to a tautology. Same rationale as
`EnforceZero` and `Core::AllocMul`. -/
def main (input : Expression (F p)) : Circuit (F p) (Var unit (F p)) := do
  let square1 ← subcircuit Mul.circuit ⟨input, input⟩
  let square2 ← subcircuit Mul.circuit ⟨square1, square1⟩
  assertZero (square2 - 1)

/-- Caller must promise `input^4 = 1` for the honest prover to satisfy
the `assertZero` constraint. Expressed as `input * input * (input * input) = 1`
to avoid HPow resolution issues on `field (F p)`. -/
def Assumptions (input : F p) (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  input * input * (input * input) = 1

/-- After the constraint, the verifier learns `input^4 = 1`. -/
def Spec (input : F p) (_output : Unit) (_data : ProverData (F p)) :=
  input * input * (input * input) = 1

instance elaborated : ElaboratedCircuit (F p) field unit where
  main
  localLength _ := 6

theorem soundness : GeneralFormalCircuit.Soundness (F p) elaborated Spec := by
  circuit_proof_start
  simp [circuit_norm, Mul.circuit, Mul.Assumptions, Mul.Spec] at h_holds ⊢
  obtain ⟨h_sq1, h_sq2, h_assert⟩ := h_holds
  rw [add_neg_eq_zero] at h_assert
  rw [h_sq1] at h_sq2
  rw [h_sq2] at h_assert
  exact h_assert

theorem completeness : GeneralFormalCircuit.Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions, Mul.Spec]
  obtain ⟨h_sq1, h_sq2⟩ := h_env
  rw [add_neg_eq_zero]
  rw [h_sq2, h_sq1]
  exact h_assumptions

def circuit : GeneralFormalCircuit (F p) field unit :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.EnforceRootOfUnity
