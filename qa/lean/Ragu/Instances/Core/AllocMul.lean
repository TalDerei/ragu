import Ragu.Circuits.Core.AllocMul
import Ragu.Instances.Autogen.Core.AllocMul
import Ragu.Core

namespace Ragu.Instances.Core.AllocMul
open Ragu.Instances.Autogen.Core.AllocMul

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var unit (F p) := ()

def serializeOutput (output : Var Circuits.Core.AllocMul.Row (F p)) : Vector (Expression (F p)) 3 :=
  #v[output.x, output.y, output.z]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := unit
  Output := Circuits.Core.AllocMul.Row

  deserializeInput
  serializeOutput

  Spec _input output := output.x * output.y = output.z

  reimplementation := Circuits.Core.AllocMul.circuit (fun _ => ⟨0, 0, 0⟩)

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm, exportedOperations,
      GeneralFormalCircuit.toSubcircuit,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
  same_spec := by
    intro input output
    dsimp only [Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.Spec]
    rfl

end Ragu.Instances.Core.AllocMul
