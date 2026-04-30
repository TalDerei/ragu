import Ragu.Circuits.Element.IsZero
import Ragu.Instances.Autogen.Element.IsZero
import Ragu.Core

namespace Ragu.Instances.Element.IsZero
open Ragu.Instances.Autogen.Element.IsZero

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var field (F p) :=
  input[0]

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.IsZero.circuit.isGeneralFormalCircuit.toWithHint

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.IsZero.circuit,
      Circuits.Element.IsZero.elaborated,
      Circuits.Element.IsZero.main,
      Circuits.Core.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.IsZero.circuit,
      Circuits.Element.IsZero.elaborated,
      Circuits.Element.IsZero.main,
      Circuits.Core.Mul.main]

end Ragu.Instances.Element.IsZero
