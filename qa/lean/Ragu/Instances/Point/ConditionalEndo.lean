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
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit
      (Circuits.Point.ConditionalEndo.circuit Circuits.Point.Spec.EpAffineParams)

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
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
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.ConditionalEndo.circuit,
      Circuits.Point.ConditionalEndo.elaborated,
      Circuits.Point.ConditionalEndo.main,
      Circuits.Boolean.ConditionalSelect.circuit,
      Circuits.Boolean.ConditionalSelect.elaborated,
      Circuits.Boolean.ConditionalSelect.main]

end Ragu.Instances.Point.ConditionalEndo
