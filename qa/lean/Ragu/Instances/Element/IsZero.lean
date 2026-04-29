import Ragu.Circuits.Element.IsZero
import Ragu.Instances.Autogen.Element.IsZero
import Ragu.Core

namespace Ragu.Instances.Element.IsZero
open Ragu.Instances.Autogen.Element.IsZero

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var field (F p) :=
  input[0]

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
      Circuits.Element.IsZero.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.IsZero.circuit,
      Circuits.Element.IsZero.elaborated,
      Circuits.Element.IsZero.main,
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
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.IsZero.circuit,
      Circuits.Element.IsZero.elaborated,
      Circuits.Element.IsZero.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]

end Ragu.Instances.Element.IsZero
