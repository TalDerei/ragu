import Ragu.Circuits.Point.AddIncomplete
import Ragu.Instances.Autogen.Point.AddIncomplete
import Ragu.Instances.Point.Hints
import Ragu.Core

namespace Ragu.Instances.Point.AddIncomplete
open Ragu.Instances.Autogen.Point.AddIncomplete

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Point.AddIncomplete.Inputs (F p) :=
  {
    P1 := ⟨input[0], input[1]⟩,
    P2 := ⟨input[2], input[3]⟩,
    nonzero := input[4]
  }

def serializeOutput (outputs : Var Circuits.Point.AddIncomplete.Outputs (F p)) : Vector (Expression (F p)) 3 :=
  #v[
    outputs.P3.x,
    outputs.P3.y,
    outputs.nonzero
  ]

def formal_instance : Core.Statements.GeneralFormalInstance where
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
    input.P1.isOnCurve Circuits.Point.Spec.EpAffineParams →
    input.P2.isOnCurve Circuits.Point.Spec.EpAffineParams →
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

  reimplementation :=
    Circuits.Point.AddIncomplete.circuit Circuits.Point.Spec.EpAffineParams
      (fun h => Hints.readRow h 0)

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm, GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.generalCircuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input;
    simp [circuit_norm, GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.generalCircuit, Circuits.Element.DivNonzero.elaborated, Circuits.Element.DivNonzero.main,
      Circuits.Core.AllocMul.circuit, Circuits.Core.AllocMul.elaborated, Circuits.Core.AllocMul.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor <;> congr)
  same_spec := by
    intro input output
    dsimp only [Circuits.Point.AddIncomplete.circuit,
      Circuits.Point.AddIncomplete.Spec]
    aesop

end Ragu.Instances.Point.AddIncomplete
