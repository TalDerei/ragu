import Ragu.Circuits.Element.Mul
import Ragu.Core

namespace Ragu.Instances.Element.Mul

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 2) : Var Circuits.Element.Mul.Input (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.Mul.circuit.isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.Mul
