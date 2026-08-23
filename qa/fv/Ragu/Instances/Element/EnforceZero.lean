import Ragu.Circuits.Element.EnforceZero
import Ragu.Core

namespace Ragu.Instances.Element.EnforceZero

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 1) : Var field (F p) :=
  input[0]

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.EnforceZero.circuit.isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.EnforceZero
