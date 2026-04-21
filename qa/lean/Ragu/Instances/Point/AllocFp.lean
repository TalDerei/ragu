import Ragu.Circuits.Point.Alloc
import Ragu.Instances.Autogen.Point.AllocFp
import Ragu.Core

namespace Ragu.Instances.Point.AllocFp
open Ragu.Instances.Autogen.Point.AllocFp

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var unit (F p) := ()

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) outputLen :=
  #v[ output.x, output.y ]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := unit
  Output := Circuits.Point.Spec.Point

  deserializeInput
  serializeOutput

  Spec input output := output.isOnCurve Circuits.Point.Spec.EpAffineParams

  reimplementation := Circuits.Point.Alloc.circuit Circuits.Point.Spec.EpAffineParams
    (fun data => ((data "alloc_square_w" 1).getD 0 default)[0])
    (fun data => ((data "alloc_square_w" 1).getD 2 default)[0])

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm, GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      Circuits.Point.Alloc.circuit, Circuits.Point.Alloc.elaborated, Circuits.Point.Alloc.main,
      Circuits.Element.AllocSquare.generalCircuit, Circuits.Element.AllocSquare.elaborated, Circuits.Element.AllocSquare.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    rfl
  same_output := by intro input; rfl
  same_spec := by intro input output; rfl

end Ragu.Instances.Point.AllocFp
