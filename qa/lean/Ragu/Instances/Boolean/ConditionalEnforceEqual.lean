import Ragu.Circuits.Boolean.ConditionalEnforceEqual
import Ragu.Instances.Autogen.Boolean.ConditionalEnforceEqual
import Ragu.Core

namespace Ragu.Instances.Boolean.ConditionalEnforceEqual
open Ragu.Instances.Autogen.Boolean.ConditionalEnforceEqual

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var Circuits.Boolean.ConditionalEnforceEqual.Input (F p) :=
  { cond := input[0], a := input[1], b := input[2] }

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Boolean.ConditionalEnforceEqual.circuit.isGeneralFormalCircuit.toWithHint

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalAssertion.isGeneralFormalCircuit,
      GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Boolean.ConditionalEnforceEqual.circuit,
      Circuits.Boolean.ConditionalEnforceEqual.elaborated,
      Circuits.Boolean.ConditionalEnforceEqual.main]
    constructor
  same_output := by
    intro input
    rfl

end Ragu.Instances.Boolean.ConditionalEnforceEqual
