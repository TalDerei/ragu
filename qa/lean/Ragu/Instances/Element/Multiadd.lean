import Ragu.Circuits.Element.Multiadd
import Ragu.Instances.Autogen.Element.Multiadd
import Ragu.Core

namespace Ragu.Instances.Element.Multiadd
open Ragu.Instances.Autogen.Element.Multiadd

/-- Coefficients chosen for this extraction instance. Must match the values
used in `qa/crates/lean_extraction/src/instances/element_multiadd.rs`. -/
def c0 : F p := 11
def c1 : F p := 13
def c2 : F p := 17

def deserializeInput (input : Vector (Expression (F p)) inputLen)
    : Var Circuits.Element.Multiadd.Input (F p) :=
  { x0 := input[0], x1 := input[1], x2 := input[2] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := Circuits.Element.Multiadd.Input
  Output := field

  deserializeInput
  serializeOutput

  Spec input output := output = c0 * input.x0 + c1 * input.x1 + c2 * input.x2

  reimplementation :=
    FormalCircuit.isGeneralFormalCircuit (F p) Circuits.Element.Multiadd.Input field
      (Circuits.Element.Multiadd.circuit c0 c1 c2)

  same_constraints := by
    intro input
    simp [Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Multiadd.circuit, Circuits.Element.Multiadd.elaborated, Circuits.Element.Multiadd.main]
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      c0, c1, c2,
      Circuits.Element.Multiadd.circuit, Circuits.Element.Multiadd.elaborated, Circuits.Element.Multiadd.main]
    rfl
  same_spec := by
    intro input output
    dsimp only [FormalCircuit.isGeneralFormalCircuit,
      Circuits.Element.Multiadd.circuit, Circuits.Element.Multiadd.Assumptions,
      Circuits.Element.Multiadd.Spec]
    aesop

end Ragu.Instances.Element.Multiadd
