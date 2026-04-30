import Clean.Circuit
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Element.EnforceRootOfUnity
variable {p : ℕ} [Fact p.Prime]

/-- `Element::enforce_root_of_unity(k)` is parameterized on `k` in Rust
and enforces `self^(2^k) = 1` by squaring `k` times. This Lean reimpl
is monomorphized to `k = 2` (enforces `self^4 = 1`): it does not
capture the full generality of the Rust gadget.

TODO: generalize to a `k`-polymorphic reimpl that mirrors the Rust
gadget's full generality (parameterize on `k : ℕ`, recurse on `k`).

Modeled as a `FormalAssertion`: the gadget is constraint-only (no
output), `Spec` acts as both assumption for completeness and conclusion for soundness,
and the constraints are an exact reformulation of the spec. -/
def main (input : Expression (F p)) : Circuit (F p) (Var unit (F p)) := do
  let square1 ← Mul.circuit ⟨input, input⟩
  let square2 ← Mul.circuit ⟨square1, square1⟩
  assertZero (square2 - 1)

def Assumptions (_ : F p) := True

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
  exact h_spec

def circuit : FormalAssertion (F p) field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.EnforceRootOfUnity
