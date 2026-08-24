import Ragu.Circuits.Element.Fold
import Ragu.Core

/-!
`Element::fold` at 0 elements. The fold of no elements is `Element::zero()`, so this trace carries **no
operations at all**: the instance pins the output expression (the zero
constant) and nothing else. Its value is that the Lean reimpl's dedicated
`n = 0` branch is compared against Rust rather than only proved.
-/

namespace Ragu.Instances.Element.FoldN0

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- Elements first, scale factor last, mirroring `element_fold.rs`. -/
def deserializeInput (input : Vector (Expression (F p)) 1)
    : Var (Circuits.Element.Fold.Input 0) (F p) :=
  { xs := #v[], s := input[0] }

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

  reimplementation := (Circuits.Element.Fold.circuit 0).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.FoldN0
