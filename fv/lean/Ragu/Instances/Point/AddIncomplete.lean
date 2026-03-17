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

  Spec input output :=
    input.P1.isOnCurve Circuits.Point.Spec.EpAffineParams → input.P2.isOnCurve Circuits.Point.Spec.EpAffineParams →
    (
      -- If the x coordinates of P1 and P2 are different, then we can conclude that the
      -- addition output is affine and is the correct result of the addition
      input.P1.x ≠ input.P2.x -> (
        (
          match input.P1.add_incomplete input.P2  with
          | none => False -- this case never happens
          | some res => output.P3 = res
        )
        ∧ output.P3.isOnCurve Circuits.Point.Spec.EpAffineParams
      )
    ) ∧
    (
      -- if the x coordinates of P1 and P2 are equal, then output nonzero is 0
      -- regardless of the input nonzero
      (input.P1.x = input.P2.x -> output.nonzero = 0) ∧

      -- if the x coordinates of P1 and P2 are not equal, then output nonzero preserves
      -- non-zero-ness from input nonzero
      (input.P1.x ≠ input.P2.x ->
        (input.nonzero = 0 -> output.nonzero = 0) ∧
        (input.nonzero ≠ 0 -> output.nonzero ≠ 0)
      )
    )

  reimplementation := Circuits.Point.AddIncomplete.circuit Circuits.Point.Spec.EpAffineParams

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm, GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input;
    simp [circuit_norm, GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor <;> congr)
  same_spec := by
    intro input output
    constructor
    · intro h h1 h2
      generalize input.P1.add_incomplete input.P2 = d at h ⊢
      cases d with
      | none => exact h h1 h2
      | some _ => exact h h1 h2
    · intro h h1 h2
      simp only [Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.Spec] at h
      generalize input.P1.add_incomplete input.P2 = d at h ⊢
      cases d with
      | none => exact h h1 h2
      | some _ => exact h h1 h2

end Ragu.Instances.Point.AddIncomplete
