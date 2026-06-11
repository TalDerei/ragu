import Ragu.Circuits.Element.EnforceNonzero
import Ragu.Core

namespace Ragu.Instances.Element.EnforceNonzero

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 1) :
    Var Circuits.Element.EnforceNonzero.Input (F p) :=
  { input := input[0], inverse := fun _ => 0 }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.EnforceNonzero.circuit

end Ragu.Instances.Element.EnforceNonzero
