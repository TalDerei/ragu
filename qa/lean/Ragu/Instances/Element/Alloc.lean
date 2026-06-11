import Ragu.Circuits.Element.Alloc
import Ragu.Core

namespace Ragu.Instances.Element.Alloc

@[reducible]
def p := Core.Primes.p

def deserializeInput (_ : Vector (Expression (F p)) 0) :
    Var (UnconstrainedDep field) (F p) :=
  fun _ => 0

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.Alloc.circuit

end Ragu.Instances.Element.Alloc
