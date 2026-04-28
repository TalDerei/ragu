import Ragu.Circuits.Element.IsEqual
import Ragu.Instances.Autogen.Element.IsEqual
import Ragu.Core

namespace Ragu.Instances.Element.IsEqual
open Ragu.Instances.Autogen.Element.IsEqual

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Element.IsEqual.Input (F p) :=
  { a := input[0], b := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  exportedOperations
  exportedOutput

  Input := Circuits.Element.IsEqual.Input
  Output := field

  Spec (input : Circuits.Element.IsEqual.Input (F p)) (output : F p) :=
    output = if input.a = input.b then 1 else 0

  deserializeInput
  serializeOutput

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit
      Circuits.Element.IsEqual.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.IsEqual.circuit,
      Circuits.Element.IsEqual.elaborated,
      Circuits.Element.IsEqual.main,
      Circuits.Element.IsZero.circuit,
      Circuits.Element.IsZero.elaborated,
      Circuits.Element.IsZero.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.IsEqual.circuit,
      Circuits.Element.IsEqual.elaborated,
      Circuits.Element.IsEqual.main,
      Circuits.Element.IsZero.circuit,
      Circuits.Element.IsZero.elaborated,
      Circuits.Element.IsZero.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.IsEqual.circuit,
      Circuits.Element.IsEqual.Assumptions,
      Circuits.Element.IsEqual.Spec]
    aesop

end Ragu.Instances.Element.IsEqual
