import Ragu.Circuits.Point.AddIncomplete
import Ragu.Core

namespace Ragu.Instances.Point.AddIncomplete
open Core.Primes

@[reducible]
def p := Core.Primes.p

@[reducible]
def inputLen := 5

@[reducible]
def outputLen := 3

set_option linter.unusedVariables false in
def exportedOperations (input_var : Var (ProvableVector field inputLen) (F p)) : Operations (F p) := [
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 0) * (var 1)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 2)))),
  Operation.assert (((var 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 4)))),
  Operation.assert (((var 1) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((input_var.get 2) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 0)))))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 3) * (var 4)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 5)))),
  Operation.assert ((((input_var.get 3) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 1))) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 5)))),
  Operation.assert ((((input_var.get 2) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 0))) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 4)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 6) * (var 7)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 8)))),
  Operation.assert (((var 6) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 3)))),
  Operation.assert (((var 7) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 3)))),
  Operation.witness 3 (fun _env => default),
  Operation.assert ((((var 9) * (var 10)) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 11)))),
  Operation.assert (((var 9) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (var 3)))),
  Operation.assert (((var 10) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * ((input_var.get 0) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 0))) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 2)))))))),
]

set_option linter.unusedVariables false in
@[reducible]
def exportedOutput (input_var : Var (ProvableVector field inputLen) (F p)) : Vector (Expression (F p)) 3 := #v[
  (((var 8) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 0))) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 2))),
  ((var 11) + ((0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 : Expression (F p)) * (input_var.get 1))),
  (var 2),
]

def deserializeInput (input : Var (ProvableVector field inputLen) (F p)) : Var Circuits.Point.AddIncomplete.Inputs (F p) :=
  {
    P1 := ⟨input.get 0, input.get 1⟩,
    P2 := ⟨input.get 2, input.get 3⟩,
    nonzero := input.get 4
  }

def serializeOutput (outputs: Var Circuits.Point.AddIncomplete.Outputs (F p)) : Vector (Expression (F p)) 3 :=
  #v[
    outputs.P3.x,
    outputs.P3.y,
    outputs.nonzero
  ]

def formal_instance : Core.Statements.FormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Point.AddIncomplete.Inputs
  Output := Circuits.Point.AddIncomplete.Outputs

  deserializeInput
  serializeOutput

  Assumptions input :=
    input.P1.isOnCurve Circuits.Point.Spec.EpAffineParams ∧ input.P2.isOnCurve Circuits.Point.Spec.EpAffineParams

  Spec input output :=
    let ⟨P1, P2, nonzero⟩ := input
    (
      -- If the x coordinates of P1 and P2 are different, then we can conclude that the
      -- addition output is affine and is the correct result of the addition
      P1.x ≠ P2.x -> (
        (
          match P1.add_incomplete P2  with
          | none => False -- this case never happens
          | some res => output.P3 = res
        )
        ∧ output.P3.isOnCurve Circuits.Point.Spec.EpAffineParams
      )
    ) ∧
    (
      -- if the x coordinates of P1 and P2 are equal, then output nonzero is 0
      -- regardless of the input nonzero
      (P1.x = P2.x -> output.nonzero = 0) ∧

      -- if the x coordinates of P1 and P2 are not equal, then output nonzero preserves
      -- non-zero-ness from input nonzero
      (P1.x ≠ P2.x ->
        (nonzero = 0 -> output.nonzero = 0) ∧
        (nonzero ≠ 0 -> output.nonzero ≠ 0)
      )
    )


  reimplementation := Circuits.Point.AddIncomplete.circuit Circuits.Point.Spec.EpAffineParams

  same_circuit := by
    intro input
    simp [Operations.toFlat, circuit_norm, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
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
      Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor <;> congr)
  same_spec := by
    intro input output;
    simp [Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.Spec]
    intro h1 h2
    aesop
  same_assumptions := by intro input; rfl


end Ragu.Instances.Point.AddIncomplete
