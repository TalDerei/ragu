import Ragu.Core

namespace Ragu.Instances.Autogen.Point.AllocFp
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 0

@[reducible]
def outputLen := 2

set_option linter.unusedVariables false in
def exportedOperations (input_var : Vector (Expression (F p)) inputLen) : Operations (F p) := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var ⟨0⟩) * (var ⟨1⟩)) + (((-1 : F p) : Expression (F p)) * (var ⟨2⟩)))),
  Operation.assert (((var ⟨0⟩) + (((-1 : F p) : Expression (F p)) * (var ⟨1⟩)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var ⟨3⟩) * (var ⟨4⟩)) + (((-1 : F p) : Expression (F p)) * (var ⟨5⟩)))),
  Operation.assert (((var ⟨3⟩) + (((-1 : F p) : Expression (F p)) * (var ⟨0⟩)))),
  Operation.assert (((var ⟨4⟩) + (((-1 : F p) : Expression (F p)) * (var ⟨2⟩)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var ⟨6⟩) * (var ⟨7⟩)) + (((-1 : F p) : Expression (F p)) * (var ⟨8⟩)))),
  Operation.assert (((var ⟨6⟩) + (((-1 : F p) : Expression (F p)) * (var ⟨7⟩)))),
  Operation.assert ((((var ⟨5⟩) + ((0x0000000000000000000000000000000000000000000000000000000000000005 : Expression (F p)) * ((1 : F p) : Expression (F p)))) + (((-1 : F p) : Expression (F p)) * (var ⟨8⟩)))),
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Vector (Expression (F p)) inputLen) : Vector (Expression (F p)) outputLen := #v[
  (var ⟨0⟩),
  (var ⟨6⟩)
]

end Ragu.Instances.Autogen.Point.AllocFp
