import Ragu.Circuits.Point.AddIncomplete
import Ragu.Core

namespace Ragu.Instances.Point.AddIncomplete

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 4) :
    Var Circuits.Point.AddIncomplete.Inputs (F p) :=
  { P1 := ⟨input[0], input[1]⟩,
    P2 := ⟨input[2], input[3]⟩,
    inverse := fun _ => 0 }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) :
    Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Point.AddIncomplete.circuit Circuits.Point.Spec.EpAffineParams

end Ragu.Instances.Point.AddIncomplete
