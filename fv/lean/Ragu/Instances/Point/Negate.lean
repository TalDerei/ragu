import Ragu.Circuits.Point.Negate
import Ragu.Instances.Autogen.Point.Negate
import Ragu.Core

namespace Ragu.Instances.Point.Negate
open Ragu.Instances.Autogen.Point.Negate

def deserializeInput (input : Vector (Expression (F p)) 2) : Var Circuits.Point.Spec.Point (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var Circuits.Point.Spec.Point (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Point.Spec.Point Circuits.Point.Spec.Point
      (Circuits.Point.Negate.circuit Circuits.Point.Spec.EpAffineParams)

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm, exportedOperations,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      Circuits.Point.Negate.circuit, Circuits.Point.Negate.elaborated, Circuits.Point.Negate.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Point.Negate.circuit, Circuits.Point.Negate.elaborated, Circuits.Point.Negate.main]
    show Expression.mul _ _ = Expression.mul _ _
    congr 1

end Ragu.Instances.Point.Negate
