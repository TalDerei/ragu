import Ragu.Circuits.Point.Alloc
import Ragu.Core

namespace Ragu.Instances.Point.AllocFp
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 0

@[reducible]
def outputLen := 2

set_option linter.unusedVariables false in
def exportedOperations (input_var : Var (ProvableVector field inputLen) (F p)) : Operations (F p) := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 0) * (var 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 2)))),
  Operation.assert (((var 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 1)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 3) * (var 4)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 5)))),
  Operation.assert (((var 3) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 0)))),
  Operation.assert (((var 4) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 2)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 6) * (var 7)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 8)))),
  Operation.assert (((var 6) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 7)))),
  Operation.assert ((((var 5) + ((0x0000000000000000000000000000000000000000000000000000000000000005 : Expression (F p)) * 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 8)))),
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Var (ProvableVector field inputLen) (F p)) : Vector (Expression (F p)) outputLen := #v[
  (var 0),
  (var 6)
]

set_option linter.unusedVariables false in
def deserializeInput (input : Var (ProvableVector field inputLen) (F p)) : Var unit (F p) := ()

def serializeOutput (output: Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) outputLen :=
  #v[
    output.x,
    output.y
  ]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := unit
  Output := Circuits.Point.Spec.Point

  deserializeInput
  serializeOutput

  Spec input output := output.isOnCurve Circuits.Point.Spec.EpAffineParams

  reimplementation := Circuits.Point.Alloc.circuit Circuits.Point.Spec.EpAffineParams
    (fun data => ((data "alloc_square_w" 1).getD 0 default)[0])
    (fun data => ((data "alloc_square_w" 1).getD 2 default)[0])

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm, GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      Circuits.Point.Alloc.circuit, Circuits.Point.Alloc.elaborated, Circuits.Point.Alloc.main,
      Circuits.Element.AllocSquare.generalCircuit, Circuits.Element.AllocSquare.elaborated, Circuits.Element.AllocSquare.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    rfl
  same_output := by intro input; rfl
  same_spec := by intro input output; rfl

end Ragu.Instances.Point.AllocFp
