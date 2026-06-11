import Ragu.Circuits.Element.AllocSquare
import Ragu.Core

namespace Ragu.Instances.Element.AllocSquare

@[reducible]
def p := Core.Primes.p

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) 0) :
    Var (UnconstrainedDep field) (F p) :=
  fun _ => 0

def serializeOutput (output : Var Circuits.Element.AllocSquare.Square (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.a, output.a_sq]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.AllocSquare.circuit

end Ragu.Instances.Element.AllocSquare
