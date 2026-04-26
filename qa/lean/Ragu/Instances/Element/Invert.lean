import Ragu.Circuits.Element.Invert
import Ragu.Instances.Autogen.Element.Invert
import Ragu.Core

namespace Ragu.Instances.Element.Invert
open Ragu.Instances.Autogen.Element.Invert

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var field (F p) :=
  input[0]

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := field
  Output := field

  deserializeInput
  serializeOutput

  Spec (input : F p) (output : F p) := input * output = 1

  reimplementation :=
    Circuits.Element.Invert.circuit (fun _ => ⟨0, 0, 0⟩)

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Invert.circuit,
      Circuits.Element.Invert.elaborated,
      Circuits.Element.Invert.main,
      Circuits.Element.InvertWith.circuit,
      Circuits.Element.InvertWith.elaborated,
      Circuits.Element.InvertWith.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Invert.circuit,
      Circuits.Element.Invert.elaborated,
      Circuits.Element.Invert.main,
      Circuits.Element.InvertWith.circuit,
      Circuits.Element.InvertWith.elaborated,
      Circuits.Element.InvertWith.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
  same_spec := by
    intro input output
    dsimp only [Circuits.Element.Invert.circuit,
      Circuits.Element.Invert.Spec]
    aesop

end Ragu.Instances.Element.Invert
