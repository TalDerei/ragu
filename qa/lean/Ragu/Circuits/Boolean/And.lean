import Clean.Circuit
import Clean.Gadgets.Boolean
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Boolean.And
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  a : F
  b : F
deriving ProvableStruct

/-- `Boolean::and` delegates the `a · b = z` gate (and the two
`enforce_equal`s binding the gate's input wires to `a` and `b`) to
`Element.Mul`, returning the gate's `z` wire as the output. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  Element.Mul.circuit { x := input.a, y := input.b }

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
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec]
  obtain ⟨ha, hb⟩ := h_assumptions
  -- h_holds : out = input_a * input_b (from Element.Mul.Spec)
  refine ⟨?_, ?_⟩
  · rw [h_holds]; exact IsBool.and_eq_val_and ha hb
  · rw [h_holds]; exact IsBool.and_is_bool ha hb

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions]

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Boolean.And
