import Ragu.Circuits.Element.InvertWith
import Ragu.Instances.Autogen.Element.InvertWith
import Ragu.Core

namespace Ragu.Instances.Element.InvertWith
open Ragu.Instances.Autogen.Element.InvertWith

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
    Circuits.Element.InvertWith.generalCircuit (fun _ => ⟨0, 0, 0⟩)

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.InvertWith.generalCircuit,
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
      Circuits.Element.InvertWith.generalCircuit,
      Circuits.Element.InvertWith.elaborated,
      Circuits.Element.InvertWith.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
  same_spec := by
    intro input output
    dsimp only [Circuits.Element.InvertWith.generalCircuit,
      Circuits.Element.InvertWith.GeneralSpec]
    aesop

end Ragu.Instances.Element.InvertWith
