import Ragu.Circuits.Point.Double
import Ragu.Core

namespace Ragu.Instances.Point.Double
open Core.Primes

@[reducible]
def CircuitField := F Core.Primes.p

def Inputs := ProvableVector field 2

-- Point doubling instance:
set_option linter.unusedVariables false in
def exported_operations (input_var : Var Inputs CircuitField) : Operations CircuitField := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 0) * (var 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 2)))),
  Operation.assert (((var 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 0)))),
  Operation.assert (((var 1) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 0)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 3) * (var 4)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 5)))),
  Operation.assert ((((0x0000000000000000000000000000000000000000000000000000000000000003 : Expression CircuitField) * (var 2)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 5)))),
  Operation.assert ((((input_var.get 1) + (input_var.get 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 4)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 6) * (var 7)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 8)))),
  Operation.assert (((var 6) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 3)))),
  Operation.assert (((var 7) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 3)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 9) * (var 10)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 11)))),
  Operation.assert (((var 9) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (var 3)))),
  Operation.assert (((var 10) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * ((input_var.get 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * ((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * ((input_var.get 0) + (input_var.get 0))))))))),
]

set_option linter.unusedVariables false in
@[reducible]
def exported_output (input_var : Var Inputs CircuitField) : Vector (Expression CircuitField) 2 := #v[
  ((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * ((input_var.get 0) + (input_var.get 0)))),
  ((var 11) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression CircuitField) * (input_var.get 1)))
]

def circuit := Circuits.Point.Double.circuit Circuits.Point.Spec.EpAffineParams (p:=Core.Primes.p)

def deserializeInput (input : Var Inputs CircuitField) : Var Circuits.Point.Spec.Point CircuitField :=
  {
    x := input.get 0,
    y := input.get 1
  }

def serializeOutput (output: Var Circuits.Point.Spec.Point CircuitField) : Vector (Expression CircuitField) 2 :=
  #v[
    output.x,
    output.y
  ]

theorem same_circuit (input : Var Inputs CircuitField):
    ((circuit (deserializeInput input)).operations 0).toFlat = (exported_operations input).toFlat := by
  simp [Operations.toFlat, circuit_norm, FormalCircuit.toSubcircuit,
    circuit, deserializeInput, exported_operations,
    Circuits.Point.Double.circuit, Circuits.Point.Double.elaborated, Circuits.Point.Double.main,
    Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
    Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
    Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
    Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  repeat (constructor; rfl)
  constructor

theorem same_output (input : Var Inputs CircuitField) :
    ((deserializeInput input) |> circuit |>.output 0 |> serializeOutput) = exported_output input:= by
  simp [circuit_norm, FormalCircuit.toSubcircuit,
    circuit, deserializeInput, serializeOutput,
    Circuits.Point.Double.circuit, Circuits.Point.Double.elaborated, Circuits.Point.Double.main,
    Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
    Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
    Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
    Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  constructor <;> rfl


end Ragu.Instances.Point.Double
