import Ragu.Circuits.Boolean.ConditionalEnforceEqual
import Ragu.Core

namespace Ragu.Instances.Boolean.ConditionalEnforceEqual

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 3) : Var Circuits.Boolean.ConditionalEnforceEqual.Input (F p) :=
  { cond := input[0], a := input[1], b := input[2] }

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Boolean.ConditionalEnforceEqual.circuit.isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Boolean.ConditionalEnforceEqual
