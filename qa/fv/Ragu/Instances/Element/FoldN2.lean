import Ragu.Circuits.Element.Fold
import Ragu.Core

/-!
`Element::fold` at 2 elements. Exactly one `Element::mul` gate — the last of the Lean reimpl's small-`n`
branches before the uniform `n >= 3` case that `FoldN3`/`N7`/`N19` pin.
-/

namespace Ragu.Instances.Element.FoldN2

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- Elements first, scale factor last, mirroring `element_fold.rs`. -/
def deserializeInput (input : Vector (Expression (F p)) 3)
    : Var (Circuits.Element.Fold.Input 2) (F p) :=
  { xs := #v[input[0], input[1]], s := input[2] }

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

  reimplementation := (Circuits.Element.Fold.circuit 2).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.FoldN2
