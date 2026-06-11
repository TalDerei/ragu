import Ragu.Circuits.Boolean.And
import Ragu.Core

namespace Ragu.Instances.Boolean.And

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 2) : Var Circuits.Boolean.And.Input (F p) :=
  { a := input[0], b := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Boolean.And.circuit.isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Boolean.And
