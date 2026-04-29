import Ragu.Circuits.Point.AddIncomplete
import Ragu.Instances.Autogen.Point.AddIncomplete
import Ragu.Core

namespace Ragu.Instances.Point.AddIncomplete
open Ragu.Instances.Autogen.Point.AddIncomplete

def deserializeInput (input : Vector (Expression (F p)) 5) : Var Circuits.Point.AddIncomplete.Inputs (F p) :=
  {
    P1 := ⟨input[0], input[1]⟩,
    P2 := ⟨input[2], input[3]⟩,
    nonzero := input[4]
  }

def serializeOutput (outputs : Var Circuits.Point.AddIncomplete.Outputs (F p)) : Vector (Expression (F p)) 3 :=
  #v[
    outputs.P3.x,
    outputs.P3.y,
    outputs.nonzero
  ]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation :=
    (Circuits.Point.AddIncomplete.circuit Circuits.Point.Spec.EpAffineParams).toWithHint

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm, GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated,
      Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main,
      Circuits.Core.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input;
    simp [circuit_norm, GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.AddIncomplete.circuit, Circuits.Point.AddIncomplete.elaborated, Circuits.Point.AddIncomplete.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated,
      Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main,
      Circuits.Core.Mul.main]
    repeat (constructor <;> congr)

end Ragu.Instances.Point.AddIncomplete
