import Ragu.Circuits.Boolean.And
import Ragu.Instances.Autogen.Boolean.And
import Ragu.Core

namespace Ragu.Instances.Boolean.And
open Ragu.Instances.Autogen.Boolean.And

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Boolean.And.Input (F p) :=
  { a := input[0], b := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Boolean.And.circuit.isGeneralFormalCircuit.toWithHint

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.And.circuit,
      Circuits.Boolean.And.elaborated,
      Circuits.Boolean.And.main,
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
      Circuits.Boolean.And.circuit,
      Circuits.Boolean.And.elaborated,
      Circuits.Boolean.And.main]

end Ragu.Instances.Boolean.And
