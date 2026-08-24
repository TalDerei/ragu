import Ragu.Circuits.Element.Fold
import Ragu.Core

/-!
`Element::fold` at 1 element. The fold of one element is that element, unchanged. Like `FoldN0` this trace
has **no operations**; it pins that the single element is passed through
rather than gated, which is the Lean reimpl's second dedicated branch.
-/

namespace Ragu.Instances.Element.FoldN1

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- Elements first, scale factor last, mirroring `element_fold.rs`. -/
def deserializeInput (input : Vector (Expression (F p)) 2)
    : Var (Circuits.Element.Fold.Input 1) (F p) :=
  { xs := #v[input[0]], s := input[1] }

/-- Writes the reimplementation's output back to the extractor's flat
output wires. -/
def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Element.Fold.circuit 1).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.FoldN1
