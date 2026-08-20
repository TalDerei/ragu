import Ragu.Circuits.Endoscalar.Extract
import Ragu.Core

namespace Ragu.Instances.Endoscalar.Extract

@[reducible]
def p := Core.Primes.p

def deserializeInput (input : Vector (Expression (F p)) 1) : Var field (F p) :=
  input[0]

def serializeOutput (output : Var (fields 128) (F p)) : Vector (Expression (F p)) 128 :=
  output

/-- Pinned at `n = 254 = Fp::CAPACITY`: the Pasta moduli are 255-bit, so
`2²⁵⁴ < p` and the 254-bit decomposition is canonical. -/
def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation :=
    (Circuits.Endoscalar.Extract.circuit 254 (by decide) (by decide)).toWithHint

end Ragu.Instances.Endoscalar.Extract
