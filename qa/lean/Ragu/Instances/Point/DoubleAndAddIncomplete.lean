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
def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  exportedOperations
  exportedOutput

  Input := Circuits.Point.DoubleAndAddIncomplete.Inputs
  Output := Circuits.Point.Spec.Point

  Spec (input : Circuits.Point.DoubleAndAddIncomplete.Inputs (F p))
       (output : Circuits.Point.Spec.Point (F p)) :=
    input.P1.isOnCurve Circuits.Point.Spec.EpAffineParams →
    input.P2.isOnCurve Circuits.Point.Spec.EpAffineParams →
    input.P1.x ≠ input.P2.x →
    (match input.P1.add_incomplete input.P2 with
     | none => False
     | some r =>
       r.x ≠ input.P1.x →
       ((match r.add_incomplete input.P1 with
         | none => False
         | some s => output = s)
        ∧ output.isOnCurve Circuits.Point.Spec.EpAffineParams))

  deserializeInput
  serializeOutput

  reimplementation :=
    Circuits.Point.DoubleAndAddIncomplete.circuit Circuits.Point.Spec.EpAffineParams
      (fun _ => ⟨0, 0, 0⟩) (fun _ => ⟨0, 0, 0⟩)

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm, exportedOperations,
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
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
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
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
    refine ⟨?_, rfl⟩
    rfl
  same_spec := by
    intro input output
    dsimp only [Circuits.Point.DoubleAndAddIncomplete.circuit,
      Circuits.Point.DoubleAndAddIncomplete.Spec]
    aesop

end Ragu.Instances.Point.DoubleAndAddIncomplete
