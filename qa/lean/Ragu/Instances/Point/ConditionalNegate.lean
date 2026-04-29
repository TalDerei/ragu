import Ragu.Circuits.Point.ConditionalNegate
import Ragu.Instances.Autogen.Point.ConditionalNegate
import Ragu.Core

namespace Ragu.Instances.Point.ConditionalNegate
open Ragu.Instances.Autogen.Point.ConditionalNegate

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Point.ConditionalNegate.Input (F p) :=
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
      Circuits.Point.ConditionalNegate.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.ConditionalNegate.circuit,
      Circuits.Point.ConditionalNegate.elaborated,
      Circuits.Point.ConditionalNegate.main,
      Circuits.Boolean.ConditionalSelect.circuit,
      Circuits.Boolean.ConditionalSelect.elaborated,
      Circuits.Boolean.ConditionalSelect.main,
      Circuits.Element.Mul.circuit,
      Circuits.Element.Mul.elaborated,
      Circuits.Element.Mul.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.ConditionalNegate.circuit,
      Circuits.Point.ConditionalNegate.elaborated,
      Circuits.Point.ConditionalNegate.main,
      Circuits.Boolean.ConditionalSelect.circuit,
      Circuits.Boolean.ConditionalSelect.elaborated,
      Circuits.Boolean.ConditionalSelect.main,
      Circuits.Element.Mul.circuit,
      Circuits.Element.Mul.elaborated,
      Circuits.Element.Mul.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]

end Ragu.Instances.Point.ConditionalNegate
