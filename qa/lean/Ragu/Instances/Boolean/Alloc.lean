import Ragu.Circuits.Boolean.Alloc
import Ragu.Instances.Autogen.Boolean.Alloc
import Ragu.Core

namespace Ragu.Instances.Boolean.Alloc
open Ragu.Instances.Autogen.Boolean.Alloc

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var unit (F p) := ()

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

-- The `same_spec` field's `intro` step exceeds the default 200k heartbeat
-- budget while reducing the subcircuit-composition goal type to whnf.
set_option maxHeartbeats 400000 in
def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  exportedOperations
  exportedOutput

  Input := unit
  Output := field

  deserializeInput
  serializeOutput

  Spec (_input : Unit) (output : F p) := output = 0 ∨ output = 1

  reimplementation :=
    Circuits.Boolean.Alloc.circuit (fun _ => false)

  same_constraints := by
    intro input
    simp only [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.Alloc.circuit,
      Circuits.Boolean.Alloc.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.main,
      circuit_norm]
    constructor
  same_output := by
    intro input
    simp only [
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Boolean.Alloc.circuit,
      Circuits.Boolean.Alloc.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.main,
      circuit_norm]
  same_spec := by
    intro input output
    dsimp only [Circuits.Boolean.Alloc.circuit,
      Circuits.Boolean.Alloc.Spec]
    aesop

end Ragu.Instances.Boolean.Alloc
