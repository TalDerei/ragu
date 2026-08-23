import Ragu.Circuits.Horner.Ky
import Ragu.Core

/-!
`ragu_circuits::horner::Horner::finish_ky` after three coefficients: the
$k(Y)$ evaluation shape `((c₀·y + c₁)·y + c₂)·y + 1`.
-/

namespace Ragu.Instances.Horner.KyN3

@[reducible]
def p := Core.Primes.p

/-- Coefficients first (highest degree first, the order they are written),
evaluation point last. -/
def deserializeInput (input : Vector (Expression (F p)) 4)
    : Var (Circuits.Horner.Ky.Input 3) (F p) :=
  { coefficients := #v[input[0], input[1], input[2]], point := input[3] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Horner.Ky.circuit 3).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Horner.KyN3
