import Ragu.Circuits.Point.Alloc
import Ragu.Instances.Autogen.Point.AllocFq
import Ragu.Core

namespace Ragu.Instances.Point.AllocFq
open Ragu.Instances.Autogen.Point.AllocFq

def deserializeInput (_ : Vector (Expression (F p)) 0) :
    Var (UnconstrainedDep Circuits.Point.Spec.Point) (F p) :=
  default

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[ output.x, output.y ]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Point.Alloc.circuit Circuits.Point.Spec.EqAffineParams

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      Circuits.Point.Alloc.circuit, Circuits.Point.Alloc.elaborated, Circuits.Point.Alloc.main,
      Circuits.Element.AllocSquare.circuit, Circuits.Element.AllocSquare.elaborated, Circuits.Element.AllocSquare.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    rfl
  same_output := by intro input; rfl

end Ragu.Instances.Point.AllocFq
