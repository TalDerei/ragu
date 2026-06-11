import Ragu.Circuits.Element.EnforceRootOfUnity
import Ragu.Core

namespace Ragu.Instances.Element.EnforceRootOfUnityK5

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 1) : Var field (F p) :=
  input[0]

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Element.EnforceRootOfUnity.circuit 5).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.EnforceRootOfUnityK5
