import Ragu.Circuits.Element.Fold
import Ragu.Core

/-!
`ragu_circuits::horner::Horner` at three coefficients. `Horner::write` is
`acc.mul(point).add(value)` for every coefficient after the first — the exact
operation trace of `Element::fold` over the same elements with `point` as the
scale factor — so the reimplementation is `Fold.circuit 3` itself and the
`Fold` soundness/completeness theorems apply to `Horner` unchanged. The
fingerprint check is what establishes that the Rust `Horner` buffer really
emits this trace.
-/

namespace Ragu.Instances.Horner.N3

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- Coefficients first (highest degree first, the order they are written),
evaluation point last — the same layout as `Element.FoldN3`. -/
def deserializeInput (input : Vector (Expression (F p)) 4)
    : Var (Circuits.Element.Fold.Input 3) (F p) :=
  { xs := #v[input[0], input[1], input[2]], s := input[3] }

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

  reimplementation := (Circuits.Element.Fold.circuit 3).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Horner.N3
