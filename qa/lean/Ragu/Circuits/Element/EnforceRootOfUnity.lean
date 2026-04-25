import Clean.Circuit
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Element.EnforceRootOfUnity
variable {p : ℕ} [Fact p.Prime]

/-- `Element::enforce_root_of_unity(k)` enforces `self^(2^k) = 1` by
squaring `k` times. This extraction instance fixes k = 2 (enforces
`self^4 = 1`). Other values of k require analogous instances with the
appropriate number of square subcircuits.

Modeled as a `FormalAssertion`: the gadget is constraint-only (no
output), `Assumptions` and `Spec` carry the same predicate, and
the constraints are an exact reformulation of that predicate. -/
def main (input : Expression (F p)) : Circuit (F p) (Var unit (F p)) := do
  let square1 ← subcircuit Mul.circuit ⟨input, input⟩
  let square2 ← subcircuit Mul.circuit ⟨square1, square1⟩
  assertZero (square2 - 1)

/-- Caller must promise `input^4 = 1` for the honest prover to satisfy
the `assertZero` constraint. Expressed as `input * input * (input * input) = 1`
to avoid HPow resolution issues on `field (F p)`. -/
def Assumptions (input : F p) :=
  input * input * (input * input) = 1

/-- The verifier learns `input^4 = 1`. -/
def Spec (input : F p) :=
  input * input * (input * input) = 1

instance elaborated : ElaboratedCircuit (F p) field unit where
  main
  localLength _ := 6

theorem soundness : FormalAssertion.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp [circuit_norm, Mul.circuit, Mul.Assumptions, Mul.Spec] at h_holds ⊢
  obtain ⟨h_sq1, h_sq2, h_assert⟩ := h_holds
  rw [add_neg_eq_zero] at h_assert
  rw [h_sq1] at h_sq2
  rw [h_sq2] at h_assert
  exact h_assert

theorem completeness : FormalAssertion.Completeness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions, Mul.Spec]
  obtain ⟨h_sq1, h_sq2⟩ := h_env
  rw [add_neg_eq_zero]
  rw [h_sq2, h_sq1]
  exact h_assumptions

def circuit : FormalAssertion (F p) field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.EnforceRootOfUnity
