import Ragu.Circuits.Point.Alloc
import Ragu.Core

namespace Ragu.Instances.Point.Alloc
open Core.Primes

@[reducible]
def CircuitField := F Core.Primes.p

def Inputs := unit

-- Point allocation instance:
set_option linter.unusedVariables false in
def exported_operations (input_var : Var Inputs CircuitField) : Operations CircuitField := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 0) * (var 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 2)))),
  Operation.assert (((var 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 1)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 3) * (var 4)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 5)))),
  Operation.assert (((var 3) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 0)))),
  Operation.assert (((var 4) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 2)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 6) * (var 7)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 8)))),
  Operation.assert (((var 6) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 7)))),
  Operation.assert ((((var 5) + ((0x0000000000000000000000000000000000000000000000000000000000000005 : Expression CircuitField) * 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 8)))),
]

set_option linter.unusedVariables false in
@[reducible]
def exported_output (input_var : Var Inputs CircuitField) : Vector (Expression CircuitField) 2 := #v[
  (var 0),
  (var 6)
]

def circuit := Circuits.Point.Alloc.circuit Circuits.Point.Spec.EpAffineParams (p:=Core.Primes.p)

set_option linter.unusedVariables false in
def deserializeInput (input : Var Inputs CircuitField) : Var unit CircuitField := ()

def serializeOutput (output: Var Circuits.Point.Spec.Point CircuitField) : Vector (Expression CircuitField) 2 :=
  #v[
    output.x,
    output.y
  ]

theorem same_circuit (input : Var Inputs CircuitField):
    ((circuit input).operations 0).toFlat = (exported_operations input).toFlat := by
  simp [Operations.toFlat, circuit_norm, FormalCircuit.toSubcircuit,
    circuit,
    Circuits.Point.Alloc.circuit, Circuits.Point.Alloc.elaborated, Circuits.Point.Alloc.main,
    Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
    Circuits.Element.AllocSquare.circuit, Circuits.Element.AllocSquare.elaborated, Circuits.Element.AllocSquare.main,
    Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  rfl

theorem same_output (input : Var Inputs CircuitField) :
  ((deserializeInput input) |> circuit |>.output 0 |> serializeOutput) = exported_output input:= by
  simp [circuit_norm,
    circuit, serializeOutput,
    Circuits.Point.Alloc.circuit, Circuits.Point.Alloc.elaborated, Circuits.Point.Alloc.main,
    Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
    Circuits.Element.AllocSquare.circuit, Circuits.Element.AllocSquare.elaborated, Circuits.Element.AllocSquare.main,
    Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  constructor <;> rfl


end Ragu.Instances.Point.Alloc
