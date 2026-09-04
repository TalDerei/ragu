import Ragu.Circuits.Boolean.Consistent
import Ragu.Core

/-!
`ragu_primitives::boolean::Boolean::enforce_consistent`: a fresh
`Boolean::alloc` seeded from the wire's own value, linked to it by one
equality — the constraint the staging machinery re-emits when it substitutes
a boolean's wire into a context where `alloc` never ran.
-/

namespace Ragu.Instances.Boolean.Consistent

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- One input wire: the boolean whose contract is re-established. -/
def deserializeInput (input : Vector (Expression (F p)) 1) : Var field (F p) :=
  input[0]

/-- An assertion returns nothing. -/
def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Boolean.Consistent.circuit.isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Boolean.Consistent
