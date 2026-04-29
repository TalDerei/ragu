import Ragu.Circuits.Element.Alloc
import Ragu.Instances.Autogen.Element.Alloc
import Ragu.Core

namespace Ragu.Instances.Element.Alloc
open Ragu.Instances.Autogen.Element.Alloc

def deserializeInput (_ : Vector (Expression (F p)) inputLen) :
    Var (UnconstrainedDep field) (F p) :=
  fun _ => 0

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.Alloc.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Alloc.circuit,
      Circuits.Element.Alloc.elaborated,
      Circuits.Element.Alloc.main,
      Circuits.Core.Mul.main]
    rfl
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Alloc.circuit,
      Circuits.Element.Alloc.elaborated,
      Circuits.Element.Alloc.main,
      Circuits.Core.Mul.main]

end Ragu.Instances.Element.Alloc
