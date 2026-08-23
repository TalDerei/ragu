import Clean.Circuit
import Clean.Gadgets.Boolean
import Ragu.Circuits.Core.Mul

namespace Ragu.Circuits.Boolean.And
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  a : F
  b : F
deriving ProvableStruct

/-- `Boolean::and` emits one mul gate (`a · b = c`) and two `enforce_equal`s
binding the gate's `a`/`b` wires to the inputs, returning the gate's `c` wire. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨a, b, c⟩ ← Core.mul fun env =>
    ⟨env input.a, env input.b, env input.a * env input.b⟩
  assertZero (a - input.a)
  assertZero (b - input.b)
  return c

/-- Caller must promise the inputs are boolean. -/
def Assumptions (input : Input (F p)) :=
  IsBool input.a ∧ IsBool input.b

/-- The output is the bitwise AND of the inputs (interpreted as `Nat`),
and is itself boolean-valued. Stated in `Bool`/`Nat` form rather than
field-multiplication form via `IsBool.and_eq_val_and`. -/
def Spec (input : Input (F p)) (out : F p) :=
  out.val = input.a.val &&& input.b.val ∧ IsBool out

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_mul, h_a, h_b⟩ := h_holds
  rw [add_neg_eq_zero] at h_a h_b
  obtain ⟨ha, hb⟩ := h_assumptions
  refine ⟨?_, ?_⟩
  · rw [← h_mul, h_a, h_b]; exact IsBool.and_eq_val_and ha hb
  · rw [← h_mul, h_a, h_b]; exact IsBool.and_is_bool ha hb

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  grind

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Boolean.And
