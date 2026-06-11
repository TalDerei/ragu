import Ragu.Circuits.Point.Alloc
import Ragu.Core

namespace Ragu.Instances.Point.AllocFq

@[reducible]
def p := Core.Primes.q

def deserializeInput (_ : Vector (Expression (F p)) 0) :
    Var (UnconstrainedDep Circuits.Point.Spec.Point) (F p) :=
  default

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[ output.x, output.y ]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Point.Alloc.circuit Circuits.Point.Spec.EqAffineParams

end Ragu.Instances.Point.AllocFq
