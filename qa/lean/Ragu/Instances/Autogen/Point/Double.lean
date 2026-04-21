import Ragu.Core

namespace Ragu.Instances.Autogen.Point.Double
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 2

@[reducible]
def outputLen := 2

set_option linter.unusedVariables false in
def exportedOperations (input_var : Vector (Expression (F p)) inputLen) : Operations (F p) := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var ⟨0⟩) * (var ⟨1⟩)) + (((-1 : F p) : Expression (F p)) * (var ⟨2⟩)))),
  Operation.assert (((var ⟨0⟩) + (((-1 : F p) : Expression (F p)) * (input_var[0])))),
  Operation.assert (((var ⟨1⟩) + (((-1 : F p) : Expression (F p)) * (input_var[0])))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var ⟨3⟩) * (var ⟨4⟩)) + (((-1 : F p) : Expression (F p)) * (var ⟨5⟩)))),
  Operation.assert ((((0x0000000000000000000000000000000000000000000000000000000000000003 : Expression (F p)) * (var ⟨2⟩)) + (((-1 : F p) : Expression (F p)) * (var ⟨5⟩)))),
  Operation.assert ((((input_var[1]) + (input_var[1])) + (((-1 : F p) : Expression (F p)) * (var ⟨4⟩)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var ⟨6⟩) * (var ⟨7⟩)) + (((-1 : F p) : Expression (F p)) * (var ⟨8⟩)))),
  Operation.assert (((var ⟨6⟩) + (((-1 : F p) : Expression (F p)) * (var ⟨3⟩)))),
  Operation.assert (((var ⟨7⟩) + (((-1 : F p) : Expression (F p)) * (var ⟨3⟩)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var ⟨9⟩) * (var ⟨10⟩)) + (((-1 : F p) : Expression (F p)) * (var ⟨11⟩)))),
  Operation.assert (((var ⟨9⟩) + (((-1 : F p) : Expression (F p)) * (var ⟨3⟩)))),
  Operation.assert (((var ⟨10⟩) + (((-1 : F p) : Expression (F p)) * ((input_var[0]) + (((-1 : F p) : Expression (F p)) * ((var ⟨8⟩) + (((-1 : F p) : Expression (F p)) * ((input_var[0]) + (input_var[0]))))))))),
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Vector (Expression (F p)) inputLen) : Vector (Expression (F p)) outputLen := #v[
  ((var ⟨8⟩) + (((-1 : F p) : Expression (F p)) * ((input_var[0]) + (input_var[0])))),
  ((var ⟨11⟩) + (((-1 : F p) : Expression (F p)) * (input_var[1])))
]

end Ragu.Instances.Autogen.Point.Double
