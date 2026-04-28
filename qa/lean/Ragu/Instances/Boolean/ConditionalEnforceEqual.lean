import Ragu.Circuits.Boolean.ConditionalEnforceEqual
import Ragu.Instances.Autogen.Boolean.ConditionalEnforceEqual
import Ragu.Core

namespace Ragu.Instances.Boolean.ConditionalEnforceEqual
open Ragu.Instances.Autogen.Boolean.ConditionalEnforceEqual

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Boolean.ConditionalEnforceEqual.Input (F p) :=
  { cond := input[0], a := input[1], b := input[2] }

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Boolean.ConditionalEnforceEqual.Input
  Output := unit

  -- High-level: when `cond = 1`, the circuit forces `a = b`. Stated
  -- unconditionally — the underlying `cond · (a - b) = 0` constraint
  -- implies this without a boolean precondition on `cond`.
  Spec (input : Circuits.Boolean.ConditionalEnforceEqual.Input (F p)) (_output : Unit) :=
    input.cond = 1 → input.a = input.b

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Boolean.ConditionalEnforceEqual.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.ConditionalEnforceEqual.circuit,
      Circuits.Boolean.ConditionalEnforceEqual.elaborated,
      Circuits.Boolean.ConditionalEnforceEqual.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    rfl
  same_spec := by
    intro input output
    dsimp only [Circuits.Boolean.ConditionalEnforceEqual.circuit,
      Circuits.Boolean.ConditionalEnforceEqual.Spec]
    aesop

end Ragu.Instances.Boolean.ConditionalEnforceEqual
