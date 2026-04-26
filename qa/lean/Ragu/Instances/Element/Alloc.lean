import Ragu.Circuits.Element.Alloc
import Ragu.Instances.Autogen.Element.Alloc
import Ragu.Core

namespace Ragu.Instances.Element.Alloc
open Ragu.Instances.Autogen.Element.Alloc

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var unit (F p) := ()

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := unit
  Output := field

  deserializeInput
  serializeOutput

  Spec (_input : Unit) (_output : F p) := True

  reimplementation :=
    Circuits.Element.Alloc.circuit (fun _ => ⟨0, 0, 0⟩)

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Alloc.circuit,
      Circuits.Element.Alloc.elaborated,
      Circuits.Element.Alloc.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
    rfl
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Alloc.circuit,
      Circuits.Element.Alloc.elaborated,
      Circuits.Element.Alloc.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
  same_spec := by
    intro input output
    dsimp only [Circuits.Element.Alloc.circuit,
      Circuits.Element.Alloc.Spec]
    aesop

end Ragu.Instances.Element.Alloc
