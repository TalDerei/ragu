import Ragu.Circuits.Point.ConditionalEndo
import Ragu.Instances.Autogen.Point.ConditionalEndo
import Ragu.Core

namespace Ragu.Instances.Point.ConditionalEndo
open Ragu.Instances.Autogen.Point.ConditionalEndo

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Point.ConditionalEndo.Input (F p) :=
  { cond := input[0], x := input[1], y := input[2] }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Point.ConditionalEndo.Input
  Output := Circuits.Point.Spec.Point

  Spec (input : Circuits.Point.ConditionalEndo.Input (F p))
       (output : Circuits.Point.Spec.Point (F p)) :=
    (input.cond = 0 ∨ input.cond = 1) →
      (output.x = input.x + input.cond * (Circuits.Point.Spec.EpAffineParams.ζ * input.x - input.x)
        ∧ output.y = input.y)

  deserializeInput
  serializeOutput

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Point.ConditionalEndo.Input Circuits.Point.Spec.Point
      (Circuits.Point.ConditionalEndo.circuit Circuits.Point.Spec.EpAffineParams)

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.ConditionalEndo.circuit,
      Circuits.Point.ConditionalEndo.elaborated,
      Circuits.Point.ConditionalEndo.main,
      Circuits.Boolean.ConditionalSelect.circuit,
      Circuits.Boolean.ConditionalSelect.elaborated,
      Circuits.Boolean.ConditionalSelect.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.ConditionalEndo.circuit,
      Circuits.Point.ConditionalEndo.elaborated,
      Circuits.Point.ConditionalEndo.main,
      Circuits.Boolean.ConditionalSelect.circuit,
      Circuits.Boolean.ConditionalSelect.elaborated,
      Circuits.Boolean.ConditionalSelect.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Point.ConditionalEndo.circuit,
      Circuits.Point.ConditionalEndo.Assumptions,
      Circuits.Point.ConditionalEndo.Spec]
    aesop

end Ragu.Instances.Point.ConditionalEndo
