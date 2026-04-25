import Clean.Circuit

namespace Ragu.Circuits.Element.EnforceZero
variable {p : ℕ} [Fact p.Prime]

def main (input : Expression (F p)) : Circuit (F p) (Var unit (F p)) := do
  assertZero input

/-- The caller must promise the input is zero. Without this, the honest
prover cannot satisfy the `assertZero` constraint — completeness fails. -/
def Assumptions (input : F p) := input = 0

/-- The constraints are an exact reformulation of the spec — for an
assertion-style gadget, soundness gives back the same predicate the
caller had to promise. -/
def Spec (input : F p) := input = 0

instance elaborated : ElaboratedCircuit (F p) field unit where
  main
  localLength _ := 0

theorem soundness : FormalAssertion.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  exact h_holds

theorem completeness : FormalAssertion.Completeness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  exact h_assumptions

def circuit : FormalAssertion (F p) field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.EnforceZero
