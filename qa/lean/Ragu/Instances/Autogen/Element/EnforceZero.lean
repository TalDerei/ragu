import Ragu.Core

namespace Ragu.Instances.Autogen.Element.EnforceZero
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 1

@[reducible]
def outputLen := 0

set_option linter.unusedVariables false in
def exportedOperations (input_var : Vector (Expression (F p)) inputLen) : Operations (F p) := [
  Operation.assert ((input_var[0])),
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Vector (Expression (F p)) inputLen) : Vector (Expression (F p)) outputLen := #v[
]

end Ragu.Instances.Autogen.Element.EnforceZero
