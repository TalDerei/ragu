import Ragu.Circuits.Element.InvertibleConsistent
import Ragu.Core

/-!
`ragu_primitives::invertible::Invertible::enforce_consistent`: a fresh
`Invertible::alloc_with_advice` seeded from the pair's own values, linked to
it wire by wire — element and inverse both, since the conservative equality
recurses into every `Gadget` field.
-/

namespace Ragu.Instances.Element.InvertibleConsistent

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- Two input wires, in `Invertible`'s field order: the element, then its
inverse. -/
def deserializeInput (input : Vector (Expression (F p)) 2) :
    Var Circuits.Element.Invertible.Pair (F p) :=
  { element := input[0], inverse := input[1] }

/-- An assertion returns nothing. -/
def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation :=
    Circuits.Element.InvertibleConsistent.circuit.isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.InvertibleConsistent
