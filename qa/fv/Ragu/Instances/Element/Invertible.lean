import Ragu.Circuits.Element.Invertible
import Ragu.Core

/-!
`ragu_primitives::invertible::Invertible::alloc_with_advice`: one mul gate
constrained `a · b = 1`, allocating an element together with its inverse.

`Invertible::alloc` shares this trace — it differs only in computing the
inverse witness before delegating, and witness bodies are not executed under
extraction.

No input wires (an allocation), and two output wires: `Invertible` derives
`Gadget` over its `element` and `inverse` fields and the extractor collects a
gadget's wires, so both are in the trace.
-/

namespace Ragu.Instances.Element.Invertible

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- No input wires: this is an allocation, so both the value and its inverse
are witness input rather than wires the caller supplies. -/
def deserializeInput (_ : Vector (Expression (F p)) 0) :
    Var (UnconstrainedDep Circuits.Element.Invertible.Pair) (F p) :=
  fun _ => ⟨0, 0⟩

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

  reimplementation := Circuits.Element.Invertible.circuit

end Ragu.Instances.Element.Invertible
