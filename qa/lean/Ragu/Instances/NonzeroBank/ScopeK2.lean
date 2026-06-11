import Ragu.Circuits.NonzeroBank.Scope
import Ragu.Core

namespace Ragu.Instances.NonzeroBank.ScopeK2

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 2) :
    Var (Circuits.NonzeroBank.Scope.Input 2) (F p) :=
  { factors := #v[input[0], input[1]], inverse := fun _ => 0 }

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.NonzeroBank.Scope.circuit 2

end Ragu.Instances.NonzeroBank.ScopeK2
