import Ragu.Circuits.Boolean.And
import Ragu.Instances.Autogen.Boolean.And
import Ragu.Core

namespace Ragu.Instances.Boolean.And
open Ragu.Instances.Autogen.Boolean.And

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Boolean.And.Input (F p) :=
  { a := input[0], b := input[1] }

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
      Circuits.Boolean.And.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      FormalCircuit.toSubcircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.And.circuit,
      Circuits.Boolean.And.elaborated,
      Circuits.Boolean.And.main,
      Circuits.Element.Mul.circuit,
      Circuits.Element.Mul.elaborated,
      Circuits.Element.Mul.main]
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      FormalCircuit.toSubcircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Boolean.And.circuit,
      Circuits.Boolean.And.elaborated,
      Circuits.Boolean.And.main,
      Circuits.Element.Mul.circuit,
      Circuits.Element.Mul.elaborated,
      Circuits.Element.Mul.main]

end Ragu.Instances.Boolean.And
