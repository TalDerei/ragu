import Ragu.Circuits.Point.Consistent
import Ragu.Core

/-!
`ragu_primitives::point::Point::enforce_consistent` on Vesta: a fresh
`Point::alloc` — the on-curve check — seeded from the point's own
coordinates, linked to it coordinate by coordinate. This is what the staging
machinery re-emits when it substitutes a point's wires into a context where
`alloc` never ran.
-/

namespace Ragu.Instances.Point.ConsistentFq

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.q

/-- Two input wires, in `Point`'s field order: `x`, then `y`. -/
def deserializeInput (input : Vector (Expression (F p)) 2) :
    Var Circuits.Point.Spec.Point (F p) :=
  { x := input[0], y := input[1] }

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
    (Circuits.Point.Consistent.circuit
      Circuits.Point.Spec.EqAffineParams
      Circuits.Point.Spec.eqAffineParams_nonzeroCoordinates).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Point.ConsistentFq
