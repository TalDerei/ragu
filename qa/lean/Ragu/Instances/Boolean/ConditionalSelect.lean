import Ragu.Circuits.Boolean.ConditionalSelect
import Ragu.Core

namespace Ragu.Instances.Boolean.ConditionalSelect

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 3) : Var Circuits.Boolean.ConditionalSelect.Input (F p) :=
  { cond := input[0], a := input[1], b := input[2] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Boolean.ConditionalSelect.circuit.isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Boolean.ConditionalSelect
