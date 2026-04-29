import Ragu.Circuits.Core.Mul
import Ragu.Instances.Autogen.Core.Mul
import Ragu.Core

namespace Ragu.Instances.Core.Mul
open Ragu.Instances.Autogen.Core.Mul

def deserializeInput (_ : Vector (Expression (F p)) inputLen) :
    Var (UnconstrainedDep Circuits.Row) (F p) :=
  default

def serializeOutput (output : Var Circuits.Row (F p)) : Vector (Expression (F p)) 3 :=
  #v[output.x, output.y, output.z]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Core.mul

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Core.Mul.main]
    rfl
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Core.Mul.main]

end Ragu.Instances.Core.Mul
