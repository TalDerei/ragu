import Ragu.Core

namespace Ragu.Instances.Autogen.Boolean.ConditionalSelect
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 3

@[reducible]
def outputLen := 1

set_option linter.unusedVariables false in
def exportedOperations (input_var : Vector (Expression (F p)) inputLen) : Operations (F p) := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var ⟨0⟩) * (var ⟨1⟩)) + (((-1 : F p) : Expression (F p)) * (var ⟨2⟩)))),
  Operation.assert (((var ⟨0⟩) + (((-1 : F p) : Expression (F p)) * (input_var[0])))),
  Operation.assert (((var ⟨1⟩) + (((-1 : F p) : Expression (F p)) * ((input_var[2]) + (((-1 : F p) : Expression (F p)) * (input_var[1])))))),
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Vector (Expression (F p)) inputLen) : Vector (Expression (F p)) outputLen := #v[
  ((input_var[1]) + (var ⟨2⟩))
]

end Ragu.Instances.Autogen.Boolean.ConditionalSelect
