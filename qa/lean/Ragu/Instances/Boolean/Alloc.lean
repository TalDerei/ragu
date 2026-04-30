import Ragu.Circuits.Boolean.Alloc
import Ragu.Instances.Autogen.Boolean.Alloc
import Ragu.Core

namespace Ragu.Instances.Boolean.Alloc
open Ragu.Instances.Autogen.Boolean.Alloc

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) inputLen) :
    Var (Unconstrained Bool) (F p) :=
  fun _ => false

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Boolean.Alloc.circuit

  same_constraints := by
    intro input
    simp only [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.Alloc.circuit,
      Circuits.Boolean.Alloc.main,
      Circuits.Core.Mul.main,
      circuit_norm]
    constructor
  same_output := by
    intro input
    simp only [
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Boolean.Alloc.circuit,
      Circuits.Boolean.Alloc.main,
      Circuits.Core.Mul.main,
      circuit_norm]

end Ragu.Instances.Boolean.Alloc
