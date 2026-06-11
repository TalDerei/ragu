import Ragu.Circuits.Point.ConditionalEndo
import Ragu.Core

namespace Ragu.Instances.Point.ConditionalEndo

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 3) : Var Circuits.Point.ConditionalEndo.Input (F p) :=
  { cond := input[0], x := input[1], y := input[2] }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Point.ConditionalEndo.circuit Circuits.Point.Spec.EpAffineParams).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Point.ConditionalEndo
