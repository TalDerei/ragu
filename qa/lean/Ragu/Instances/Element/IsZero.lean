import Ragu.Circuits.Element.IsZero
import Ragu.Core

namespace Ragu.Instances.Element.IsZero

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 1) : Var field (F p) :=
  input[0]

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.IsZero.circuit.isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.IsZero
