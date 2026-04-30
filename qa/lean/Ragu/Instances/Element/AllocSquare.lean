import Ragu.Circuits.Element.AllocSquare
import Ragu.Instances.Autogen.Element.AllocSquare
import Ragu.Core

namespace Ragu.Instances.Element.AllocSquare
open Ragu.Instances.Autogen.Element.AllocSquare

set_option linter.unusedVariables false in
def deserializeInput (input : Vector (Expression (F p)) inputLen) :
    Var (UnconstrainedDep field) (F p) :=
  fun _ => 0

def serializeOutput (output : Var Circuits.Element.AllocSquare.Square (F p)) : Vector (Expression (F p)) 2 :=
  #v[output.a, output.a_sq]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.AllocSquare.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.AllocSquare.circuit,
      Circuits.Element.AllocSquare.elaborated,
      Circuits.Element.AllocSquare.main,
      Circuits.Core.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    simp [circuit_norm,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.AllocSquare.circuit,
      Circuits.Element.AllocSquare.elaborated,
      Circuits.Element.AllocSquare.main,
      Circuits.Core.Mul.main]

end Ragu.Instances.Element.AllocSquare
