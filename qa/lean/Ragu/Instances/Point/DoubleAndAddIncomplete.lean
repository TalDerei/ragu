import Ragu.Circuits.Point.DoubleAndAddIncomplete
import Ragu.Instances.Autogen.Point.DoubleAndAddIncomplete
import Ragu.Core

namespace Ragu.Instances.Point.DoubleAndAddIncomplete
open Ragu.Instances.Autogen.Point.DoubleAndAddIncomplete

def deserializeInput (input : Vector (Expression (F p)) inputLen)
    : Var Circuits.Point.DoubleAndAddIncomplete.Inputs (F p) :=
  { P1 := { x := input[0], y := input[1] },
    P2 := { x := input[2], y := input[3] } }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p))
    : Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

set_option maxHeartbeats 800000 in
def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation :=
    (Circuits.Point.DoubleAndAddIncomplete.circuit Circuits.Point.Spec.EpAffineParams).toWithHint

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm, exportedOperations,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      FormalCircuit.toSubcircuit,
      deserializeInput,
      Circuits.Point.DoubleAndAddIncomplete.circuit,
      Circuits.Point.DoubleAndAddIncomplete.elaborated,
      Circuits.Point.DoubleAndAddIncomplete.main,
      Circuits.Element.DivNonzero.circuit,
      Circuits.Element.DivNonzero.elaborated,
        Circuits.Element.DivNonzero.main,
      Circuits.Element.Square.circuit,
      Circuits.Element.Square.elaborated,
      Circuits.Element.Square.main,
      Circuits.Element.Mul.circuit,
      Circuits.Element.Mul.elaborated,
      Circuits.Element.Mul.main,
      Circuits.Core.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.DoubleAndAddIncomplete.circuit,
      Circuits.Point.DoubleAndAddIncomplete.elaborated,
      Circuits.Point.DoubleAndAddIncomplete.main,
      Circuits.Element.DivNonzero.circuit,
      Circuits.Element.DivNonzero.elaborated,
        Circuits.Element.DivNonzero.main,
      Circuits.Element.Square.circuit,
      Circuits.Element.Square.elaborated,
      Circuits.Element.Square.main,
      Circuits.Element.Mul.circuit,
      Circuits.Element.Mul.elaborated,
      Circuits.Element.Mul.main,
      Circuits.Core.Mul.main]
    refine ⟨?_, rfl⟩
    rfl

end Ragu.Instances.Point.DoubleAndAddIncomplete
