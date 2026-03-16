import Ragu.Circuits.Point.Double
import Ragu.Core

namespace Ragu.Instances.Point.Double
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 2

@[reducible]
def outputLen := 2

set_option linter.unusedVariables false in
def exportedOperations (input_var : Var (ProvableVector field inputLen) (F p)) : Operations (F p) := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 0) * (var 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 2)))),
  Operation.assert (((var 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 0)))),
  Operation.assert (((var 1) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 0)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 3) * (var 4)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 5)))),
  Operation.assert ((((0x0000000000000000000000000000000000000000000000000000000000000003 : Expression (F p)) * (var 2)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 5)))),
  Operation.assert ((((input_var.get 1) + (input_var.get 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 4)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 6) * (var 7)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 8)))),
  Operation.assert (((var 6) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 3)))),
  Operation.assert (((var 7) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 3)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 9) * (var 10)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 11)))),
  Operation.assert (((var 9) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 3)))),
  Operation.assert (((var 10) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((input_var.get 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((input_var.get 0) + (input_var.get 0))))))))),
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Var (ProvableVector field inputLen) (F p)) : Vector (Expression (F p)) 2 := #v[
  ((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((input_var.get 0) + (input_var.get 0)))),
  ((var 11) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 1)))
]

def deserializeInput (input : Var (ProvableVector field inputLen) (F p)) : Var Circuits.Point.Spec.Point (F p) :=
  {
    x := input.get 0,
    y := input.get 1
  }

def serializeOutput (output: Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[
    output.x,
    output.y
  ]

def formal_instance : Core.Statements.FormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Point.Spec.Point
  Output := Circuits.Point.Spec.Point

  deserializeInput
  serializeOutput

  Assumptions input :=
    input.isOnCurve Circuits.Point.Spec.EpAffineParams ∧
    Circuits.Point.Spec.EpAffineParams.noOrderTwoPoints

  Spec input output :=
    (match input.double with
    | none => False -- this case never happens
    | some double => output = double)
    ∧
    output.isOnCurve Circuits.Point.Spec.EpAffineParams


  reimplementation := Circuits.Point.Double.circuit Circuits.Point.Spec.EpAffineParams

  same_circuit := by
    intro input
    simp [Operations.toFlat, circuit_norm, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.Double.circuit, Circuits.Point.Double.elaborated, Circuits.Point.Double.main,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input;
    simp [circuit_norm, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.Double.circuit, Circuits.Point.Double.elaborated, Circuits.Point.Double.main,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    constructor <;> rfl
  same_spec := by
    intro input output;
    simp [Circuits.Point.Double.circuit, Circuits.Point.Double.Spec]
    intro h1
    aesop
  same_assumptions := by intro input; rfl

end Ragu.Instances.Point.Double
