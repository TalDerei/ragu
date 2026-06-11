import Ragu.Circuits.Point.DoubleAndAddIncomplete
import Ragu.Core

namespace Ragu.Instances.Point.DoubleAndAddIncomplete

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 4)
    : Var Circuits.Point.DoubleAndAddIncomplete.Inputs (F p) :=
  { P1 := { x := input[0], y := input[1] },
    P2 := { x := input[2], y := input[3] },
    inverse := fun _ => 0 }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p))
    : Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation :=
    Circuits.Point.DoubleAndAddIncomplete.circuit Circuits.Point.Spec.EpAffineParams

end Ragu.Instances.Point.DoubleAndAddIncomplete
