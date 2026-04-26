import Ragu.Circuits.Element.Fold
import Ragu.Instances.Autogen.Element.Fold
import Ragu.Core

namespace Ragu.Instances.Element.Fold
open Ragu.Instances.Autogen.Element.Fold

def deserializeInput (input : Vector (Expression (F p)) inputLen)
    : Var Circuits.Element.Fold.Input (F p) :=
  { x0 := input[0], x1 := input[1], x2 := input[2], s := input[3] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Element.Fold.Input
  Output := field

  deserializeInput
  serializeOutput

  Spec input output :=
    output = (input.x0 * input.s + input.x1) * input.s + input.x2

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Element.Fold.Input field
      Circuits.Element.Fold.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Fold.circuit, Circuits.Element.Fold.elaborated, Circuits.Element.Fold.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Fold.circuit, Circuits.Element.Fold.elaborated, Circuits.Element.Fold.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Fold.circuit, Circuits.Element.Fold.Assumptions,
      Circuits.Element.Fold.Spec]
    aesop

end Ragu.Instances.Element.Fold
