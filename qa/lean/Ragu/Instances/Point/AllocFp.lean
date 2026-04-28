import Ragu.Circuits.Point.Alloc
import Ragu.Instances.Autogen.Point.AllocFp
import Ragu.Instances.Point.Hints
import Ragu.Core

namespace Ragu.Instances.Point.AllocFp
open Ragu.Instances.Autogen.Point.AllocFp

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) 0) : Var unit (F p) := ()

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[ output.x, output.y ]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  -- x reads row 0 from "alloc_square_w", y reads row 2.
  reimplementation := Circuits.Point.Alloc.circuit Circuits.Point.Spec.EpAffineParams
    (fun h => Hints.readSquareElem h 0 0)
    (fun h => Hints.readSquareElem h 2 0)

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm, GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      Circuits.Point.Alloc.circuit, Circuits.Point.Alloc.elaborated, Circuits.Point.Alloc.main,
      Circuits.Element.AllocSquare.circuit, Circuits.Element.AllocSquare.elaborated, Circuits.Element.AllocSquare.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    rfl
  same_output := by intro input; rfl

end Ragu.Instances.Point.AllocFp
