import Ragu.Circuits.NonzeroBank.Scope
import Ragu.Core

/-!
`NonzeroBank::scope` over 0 factors. An empty scope still discharges: the bank's initial product `1` is
constrained nonzero, so the trace is one gate plus the discharge. The Lean
reimpl splits `K = 0` from `K + 1` because `Fin 0` is not `Inhabited`, and
without this instance that branch is proved but never fingerprinted.

The `Spec` at `K = 0` quantifies over `Fin 0` and so is vacuously true; what
this instance pins is the *trace* — that an empty scope really does emit the
discharge rather than nothing.
-/

namespace Ragu.Instances.NonzeroBank.ScopeK0

/-- The prime this instance is fixed at. -/
@[reducible]
def p := Core.Primes.p

/-- The folded factors; the inverse of their product is prover advice. -/
def deserializeInput (_input : Vector (Expression (F p)) 0) :
    Var (Circuits.NonzeroBank.Scope.Input 0) (F p) :=
  { factors := #v[], inverse := fun _ => 0 }

/-- The scope returns nothing; its content is the constraints it emits. -/
def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

/-- The formal instance the fingerprint check compares against the Rust
extractor's trace. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.NonzeroBank.Scope.circuit 0

end Ragu.Instances.NonzeroBank.ScopeK0
