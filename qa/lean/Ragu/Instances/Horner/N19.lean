import Ragu.Circuits.Element.Fold
import Ragu.Core

/-!
`ragu_circuits::horner::Horner` at nineteen coefficients, the `NumGroups`
shape `fold_revdot.rs` uses for the outer layer. See
`Ragu.Instances.Horner.N3` for why the reimplementation is `Fold.circuit`
itself.
-/

namespace Ragu.Instances.Horner.N19

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 20)
    : Var (Circuits.Element.Fold.Input 19) (F p) :=
  { xs := #v[input[0], input[1], input[2], input[3], input[4], input[5],
         input[6], input[7], input[8], input[9], input[10], input[11],
         input[12], input[13], input[14], input[15], input[16], input[17],
         input[18]],
    s := input[19] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Element.Fold.circuit 19).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Horner.N19
