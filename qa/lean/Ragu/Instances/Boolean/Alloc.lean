import Ragu.Circuits.Boolean.Alloc
import Ragu.Core

namespace Ragu.Instances.Boolean.Alloc

@[reducible]
def p := Core.Primes.p

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) 0) :
    Var (Unconstrained Bool) (F p) :=
  fun _ => false

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := Circuits.Boolean.Alloc.circuit

end Ragu.Instances.Boolean.Alloc
