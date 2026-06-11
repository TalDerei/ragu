import Ragu.Circuits.Point.Alloc
import Ragu.Core

namespace Ragu.Instances.Point.AllocFp

@[reducible]
def p := Core.Primes.p

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) 0) :
    Var (UnconstrainedDep Circuits.Point.Spec.Point) (F p) :=
  default

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[ output.x, output.y ]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Point.Alloc.circuit Circuits.Point.Spec.EpAffineParams

end Ragu.Instances.Point.AllocFp
