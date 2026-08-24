import Ragu.Circuits.Element.EnforceInvertible
import Ragu.Core

/-!
`ragu_primitives::element::Element::enforce_invertible_with`: allocate an
`Invertible` pair and link its element to the caller's wire.
`Element::enforce_invertible` shares the trace, differing only in computing
the inverse witness itself.

The operations are `Element.EnforceNonzero`'s — Rust's `enforce_nonzero` is
`enforce_invertible(...).into_element()` — but the collected wires are not:
`Invertible` carries two, `Nonzero` one. This instance is what ties the
second gate wire to the inverse.
-/

namespace Ragu.Instances.Element.EnforceInvertible

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- One input wire: the element being constrained invertible. The inverse is
prover advice, not a wire the caller supplies. -/
def deserializeInput (input : Vector (Expression (F p)) 1) :
    Var Circuits.Element.EnforceInvertible.Input (F p) :=
  { element := input[0], inverse := fun _ => 0 }

/-- Writes the element and inverse wires back to the extractor's flat output
wires, in the field order `Invertible` declares them. -/
def serializeOutput (output : Var Circuits.Element.Invertible.Pair (F p)) :
    Vector (Expression (F p)) 2 :=
  #v[output.element, output.inverse]

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.EnforceInvertible.circuit

end Ragu.Instances.Element.EnforceInvertible
