import Ragu.Circuits.Element.EnforceZero
import Ragu.Instances.Autogen.Element.EnforceZero
import Ragu.Core

namespace Ragu.Instances.Element.EnforceZero
open Ragu.Instances.Autogen.Element.EnforceZero

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var field (F p) :=
  input[0]

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Element.EnforceZero.circuit.isGeneralFormalCircuit.toWithHint

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalAssertion.isGeneralFormalCircuit,
      GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.EnforceZero.circuit, Circuits.Element.EnforceZero.elaborated, Circuits.Element.EnforceZero.main]
  same_output := by
    intro input
    rfl

end Ragu.Instances.Element.EnforceZero
