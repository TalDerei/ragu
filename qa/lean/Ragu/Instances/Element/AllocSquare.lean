import Ragu.Circuits.Element.AllocSquare
import Ragu.Instances.Autogen.Element.AllocSquare
import Ragu.Core

namespace Ragu.Instances.Element.AllocSquare
open Ragu.Instances.Autogen.Element.AllocSquare

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var unit (F p) := ()

def serializeOutput (output : Var Circuits.Element.AllocSquare.Square (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.a, output.a_sq]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  exportedOperations
  exportedOutput

  Input := unit
  Output := Circuits.Element.AllocSquare.Square

  deserializeInput
  serializeOutput

  Spec _input output := output.a_sq = output.a^2

  reimplementation := Circuits.Element.AllocSquare.circuit (fun _ => 0)

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.AllocSquare.circuit,
      Circuits.Element.AllocSquare.elaborated,
      Circuits.Element.AllocSquare.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.AllocSquare.circuit,
      Circuits.Element.AllocSquare.elaborated,
      Circuits.Element.AllocSquare.main,
      Circuits.Core.AllocMul.circuit,
      Circuits.Core.AllocMul.elaborated,
      Circuits.Core.AllocMul.main]
  same_spec := by
    intro input output
    dsimp only [Circuits.Element.AllocSquare.circuit,
      Circuits.Element.AllocSquare.Spec]
    aesop

end Ragu.Instances.Element.AllocSquare
