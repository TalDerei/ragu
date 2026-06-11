import Ragu.Circuits.Core.Mul
import Ragu.Core

namespace Ragu.Instances.Core.Mul

@[reducible]
def p := Core.Primes.p

def deserializeInput (_ : Vector (Expression (F p)) 0) :
    Var (UnconstrainedDep Circuits.Row) (F p) :=
  default

def serializeOutput (output : Var Circuits.Row (F p)) : Vector (Expression (F p)) 3 :=
  #v[output.x, output.y, output.z]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Core.mul

end Ragu.Instances.Core.Mul
