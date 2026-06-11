import Ragu.Circuits.Point.ConditionalNegate
import Ragu.Core

namespace Ragu.Instances.Point.ConditionalNegate

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 3) : Var Circuits.Point.ConditionalNegate.Input (F p) :=
  { cond := input[0], x := input[1], y := input[2] }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Point.ConditionalNegate.circuit.isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Point.ConditionalNegate
