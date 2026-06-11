import Ragu.Circuits.Element.Fold
import Ragu.Core

namespace Ragu.Instances.Element.FoldN7

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 8)
    : Var (Circuits.Element.Fold.Input 7) (F p) :=
  { xs := #v[input[0], input[1], input[2], input[3], input[4], input[5], input[6]],
    s := input[7] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Element.Fold.circuit 7).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.FoldN7
