import Ragu.Circuits.Element.Fold
import Ragu.Instances.Autogen.Element.FoldN3
import Ragu.Core

namespace Ragu.Instances.Element.FoldN3
open Ragu.Instances.Autogen.Element.FoldN3

def deserializeInput (input : Vector (Expression (F p)) inputLen)
    : Var (Circuits.Element.Fold.Input 3) (F p) :=
  { xs := #v[input[0], input[1], input[2]], s := input[3] }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) 1 :=
  #v[output]

def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := (Circuits.Element.Fold.circuit 3).isGeneralFormalCircuit.toWithHint

  same_constraints := by
    intro input
    simp [Core.Statements.FlatOperation.eraseCompute, List.map,
      Operations.toFlat, circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, exportedOperations,
      Circuits.Element.Fold.circuit,
      Circuits.Element.Fold.elaborated,
      Circuits.Element.Fold.main,
      Circuits.Element.Fold.hornerStep,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    rfl
  same_output := by
    intro input
    simp [circuit_norm,
      FormalCircuit.isGeneralFormalCircuit,
      GeneralFormalCircuit.toWithHint,
      GeneralFormalCircuit.WithHint.toSubcircuit, FormalCircuit.toSubcircuit,
      deserializeInput, serializeOutput,
      Circuits.Element.Fold.circuit,
      Circuits.Element.Fold.elaborated,
      Circuits.Element.Fold.main,
      Circuits.Element.Fold.hornerStep,
      Circuits.Element.Mul.circuit, Circuits.Element.Mul.elaborated, Circuits.Element.Mul.main]
    rfl

end Ragu.Instances.Element.FoldN3
