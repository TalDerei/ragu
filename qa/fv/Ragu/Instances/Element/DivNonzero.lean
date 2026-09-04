import Ragu.Circuits.Element.DivNonzero
import Ragu.Core

namespace Ragu.Instances.Element.DivNonzero

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 2) :
    Var Circuits.Element.DivNonzero.Input (F p) :=
  { x := input[0], y := input[1], inverse := fun _ => 0 }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.DivNonzero.circuit

end Ragu.Instances.Element.DivNonzero
