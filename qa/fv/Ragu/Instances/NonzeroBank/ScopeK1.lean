import Ragu.Circuits.NonzeroBank.Scope
import Ragu.Core

/-!
`NonzeroBank::scope` over 1 factor. A single fold: the smallest case that goes through the `Circuit.foldl` body,
and the smallest `K` at which the `Spec` says something (the one factor is
nonzero).
-/

namespace Ragu.Instances.NonzeroBank.ScopeK1

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- The folded factors; the inverse of their product is prover advice. -/
def deserializeInput (input : Vector (Expression (F p)) 1) :
    Var (Circuits.NonzeroBank.Scope.Input 1) (F p) :=
  { factors := #v[input[0]], inverse := fun _ => 0 }

/-- The scope returns nothing; its content is the constraints it emits. -/
def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.NonzeroBank.Scope.circuit 1

end Ragu.Instances.NonzeroBank.ScopeK1
