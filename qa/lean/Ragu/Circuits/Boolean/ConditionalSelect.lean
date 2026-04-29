import Clean.Circuit
import Clean.Gadgets.Boolean
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Boolean.ConditionalSelect
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  cond : F
  a : F
  b : F
deriving ProvableStruct

/-- `Boolean::conditional_select(a, b)` emits one mul gate producing
`cond * (b - a)`, with the two factor wires constrained via
`enforce_equal` to `cond` and `b - a` respectively. The returned
element is the virtual expression `a + cond * (b - a)`. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  let cond_times_diff ← Element.Mul.circuit ⟨input.cond, input.b - input.a⟩
  return input.a + cond_times_diff

/-- Caller must promise `cond` is boolean — without it, the "select"
description below doesn't hold (the underlying circuit computes
`a + cond · (b - a)`, which only collapses to a select when `cond ∈ {0, 1}`). -/
def Assumptions (input : Input (F p)) :=
  IsBool input.cond

/-- High-level operation: select `b` when `cond = 1`, else `a`. -/
def Spec (input : Input (F p)) (out : F p) :=
  out = if input.cond = 1 then input.b else input.a

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  output input offset := input.a + varFromOffset field (offset + 2)
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec]
  -- The output is `input_a + cond_times_diff`, where the subcircuit spec gives
  -- `cond_times_diff = input_cond * (input_b - input_a)`.
  rcases h_assumptions with hc0 | hc1
  · rw [hc0, if_neg (by norm_num : (0 : F p) ≠ 1), h_holds, hc0]
    ring
  · rw [hc1, if_pos rfl, h_holds, hc1]
    ring

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions]

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Boolean.ConditionalSelect
