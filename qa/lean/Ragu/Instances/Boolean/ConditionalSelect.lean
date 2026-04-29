import Ragu.Circuits.Boolean.ConditionalSelect
import Ragu.Instances.Autogen.Boolean.ConditionalSelect
import Ragu.Core

namespace Ragu.Instances.Boolean.ConditionalSelect
open Ragu.Instances.Autogen.Boolean.ConditionalSelect

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Boolean.ConditionalSelect.Input (F p) :=
  { cond := input[0], a := input[1], b := input[2] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit
      Circuits.Boolean.ConditionalSelect.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
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
      Circuits.Boolean.ConditionalSelect.circuit,
      Circuits.Boolean.ConditionalSelect.elaborated,
      Circuits.Boolean.ConditionalSelect.main,
      Circuits.Element.Mul.circuit,
      Circuits.Element.Mul.elaborated,
      Circuits.Element.Mul.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]

end Ragu.Instances.Boolean.ConditionalSelect
