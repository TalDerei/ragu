import Ragu.Circuits.Point.Double
import Ragu.Core

namespace Ragu.Instances.Point.Double

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 2) : Var Circuits.Point.Spec.Point (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[ output.x, output.y ]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Point.Double.circuit Circuits.Point.Spec.EpAffineParams).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Point.Double
