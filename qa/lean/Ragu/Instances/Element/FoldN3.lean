import Ragu.Circuits.Element.Fold
import Ragu.Core

namespace Ragu.Instances.Element.FoldN3

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 4)
    : Var (Circuits.Element.Fold.Input 3) (F p) :=
  { xs := #v[input[0], input[1], input[2]], s := input[3] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Element.Fold.circuit 3).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Element.FoldN3
