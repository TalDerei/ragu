import Ragu.Circuits.Element.EnforceZero
import Ragu.Instances.Autogen.Element.EnforceZero
import Ragu.Core

namespace Ragu.Instances.Element.EnforceZero
open Ragu.Instances.Autogen.Element.EnforceZero

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var field (F p) :=
  input[0]

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  exportedOperations
  exportedOutput

  Input := field
  Output := unit

  deserializeInput
  serializeOutput

  Spec (input : F p) (_output : Unit) := input = 0

  reimplementation :=
    FormalAssertion.isGeneralFormalCircuit
      Circuits.Element.EnforceZero.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalAssertion.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.EnforceZero.circuit, Circuits.Element.EnforceZero.elaborated, Circuits.Element.EnforceZero.main]
  same_output := by
    intro input
    rfl
  same_spec := by
    intro input output
    dsimp only [FormalAssertion.isGeneralFormalCircuit,
      Circuits.Element.EnforceZero.circuit,
      Circuits.Element.EnforceZero.Assumptions,
      Circuits.Element.EnforceZero.Spec]
    aesop

end Ragu.Instances.Element.EnforceZero
