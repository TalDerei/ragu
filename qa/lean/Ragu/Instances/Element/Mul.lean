import Ragu.Circuits.Element.Mul
import Ragu.Instances.Autogen.Element.Mul
import Ragu.Core

namespace Ragu.Instances.Element.Mul
open Ragu.Instances.Autogen.Element.Mul

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Element.Mul.Input (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Element.Mul.Input
  Output := field

  deserializeInput
  serializeOutput

  Spec input output := output = input.x * input.y

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Element.Mul.Input field
      Circuits.Element.Mul.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.Assumptions,
      Circuits.Element.Mul.Spec]
    aesop

end Ragu.Instances.Element.Mul
