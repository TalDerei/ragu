import Ragu.Circuits.Point.Double
import Ragu.Instances.Autogen.Point.Double
import Ragu.Core

namespace Ragu.Instances.Point.Double
open Ragu.Instances.Autogen.Point.Double

def deserializeInput (input : Vector (Expression (F p)) 2) : Var Circuits.Point.Spec.Point (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[ output.x, output.y ]

set_option maxHeartbeats 800000 in
def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Point.Double.circuit Circuits.Point.Spec.EpAffineParams).isGeneralFormalCircuit.toWithHint

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm, GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      FormalCircuit.isGeneralFormalCircuit,
      deserializeInput, exportedOperations,
      Circuits.Point.Double.circuit, Circuits.Point.Double.elaborated, Circuits.Point.Double.main,
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
      FormalCircuit.isGeneralFormalCircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.Double.circuit, Circuits.Point.Double.elaborated, Circuits.Point.Double.main,
      Circuits.Element.Square.circuit, Circuits.Element.Square.elaborated, Circuits.Element.Square.main,
      Circuits.Element.DivNonzero.circuit, Circuits.Element.DivNonzero.elaborated,
      Circuits.Element.DivNonzero.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    constructor <;> rfl
end Ragu.Instances.Point.Double
