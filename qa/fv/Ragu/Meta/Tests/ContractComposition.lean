import Ragu.Circuits.Boolean.And

/-!
# Contract-composition regression tests

The example checks that the child postcondition is not available as an
unconditional fact, then shows that the parent can consume it after carrying
the child's assumptions.
-/

namespace Ragu.Meta.Tests.ContractComposition

open Ragu.Circuits

variable {p : ℕ} [Fact p.Prime]

def parentMain (input : Var Boolean.And.Input (F p)) :
    Circuit (F p) (Expression (F p)) :=
  Boolean.And.circuit input

instance parentElaborated :
    ElaboratedCircuit (F p) Boolean.And.Input field parentMain := by
  unfold parentMain
  elaborate_circuit

example : Soundness (F p) (Input := Boolean.And.Input) (Output := field)
    parentMain Boolean.And.Assumptions Boolean.And.Spec := by
  circuit_proof_start
    [parentMain, Boolean.And.circuit, Boolean.And.Assumptions, Boolean.And.Spec]
  -- The child postcondition is not available until its assumptions are
  -- supplied.
  fail_if_success exact h_holds
  exact h_holds h_assumptions

end Ragu.Meta.Tests.ContractComposition
