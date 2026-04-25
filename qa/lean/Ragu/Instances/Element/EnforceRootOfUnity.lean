import Ragu.Circuits.Element.EnforceRootOfUnity
import Ragu.Instances.Autogen.Element.EnforceRootOfUnity
import Ragu.Core

namespace Ragu.Instances.Element.EnforceRootOfUnity
open Ragu.Instances.Autogen.Element.EnforceRootOfUnity

def deserializeInput (input : Vector (Expression (F p)) inputLen) : Var field (F p) :=
  input[0]

def serializeOutput (_output : Var unit (F p)) : Vector (Expression (F p)) 0 :=
  #v[]

def formal_instance : Core.Statements.GeneralFormalInstance where
  p
  inputLen
  outputLen
  exportedOperations
  exportedOutput

  Input := field
  Output := unit

  deserializeInput
  serializeOutput

  -- After the constraint, input⁴ = 1. Expressed as `input * input * (input *
  -- input)` (not `input^4`) to avoid HPow resolution issues on `field (F p)`.
  Spec (input : F p) (_output : Unit) :=
    input * input * (input * input) = 1
      → input * input * (input * input) = 1

  reimplementation :=
    FormalAssertion.isGeneralFormalCircuit (F p) field
      Circuits.Element.EnforceRootOfUnity.circuit

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalAssertion.isGeneralFormalCircuit,
      GeneralFormalCircuit.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.EnforceRootOfUnity.circuit,
      Circuits.Element.EnforceRootOfUnity.elaborated,
      Circuits.Element.EnforceRootOfUnity.main,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    repeat (constructor; rfl)
    constructor
  same_output := by
    intro input
    rfl
  same_spec := by
    intro input output
    dsimp only [FormalAssertion.isGeneralFormalCircuit,
      Circuits.Element.EnforceRootOfUnity.circuit,
      Circuits.Element.EnforceRootOfUnity.Assumptions,
      Circuits.Element.EnforceRootOfUnity.Spec]
    aesop

end Ragu.Instances.Element.EnforceRootOfUnity
