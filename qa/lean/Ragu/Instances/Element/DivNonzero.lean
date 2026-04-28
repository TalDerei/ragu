import Ragu.Circuits.Element.DivNonzero
import Ragu.Instances.Autogen.Element.DivNonzero
import Ragu.Core

namespace Ragu.Instances.Element.DivNonzero
open Ragu.Instances.Autogen.Element.DivNonzero

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Element.DivNonzero.Inputs (F p) :=
  { x := input[0], y := input[1] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Element.DivNonzero.Inputs
  Output := field

  deserializeInput
  serializeOutput

  -- See `Circuits/Element/DivNonzero.lean` for the rationale behind the
  -- `y ≠ 0 ∨ x ≠ 0` premise.
  Spec input output :=
    input.y ≠ 0 ∨ input.x ≠ 0 → output = input.x / input.y

  reimplementation :=
    Circuits.Element.DivNonzero.circuit (fun _ => ⟨0, 0, 0⟩)

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.DivNonzero.circuit,
      Circuits.Element.DivNonzero.elaborated,
      Circuits.Element.DivNonzero.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.DivNonzero.circuit,
      Circuits.Element.DivNonzero.elaborated,
      Circuits.Element.DivNonzero.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
  same_spec := by
    intro input output
    dsimp only [Circuits.Element.DivNonzero.circuit,
      Circuits.Element.DivNonzero.Spec]
    aesop

end Ragu.Instances.Element.DivNonzero
