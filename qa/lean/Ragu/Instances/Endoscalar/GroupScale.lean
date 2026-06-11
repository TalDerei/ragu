import Ragu.Circuits.Endoscalar.GroupScale
import Ragu.Instances.Autogen.Endoscalar.GroupScale
import Ragu.CircuitFlattening
import Ragu.Core

namespace Ragu.Instances.Endoscalar.GroupScale
open Ragu.Instances.Autogen.Endoscalar.GroupScale

/-- Deserialize the flat 130-wire input: first 128 are endoscalar bits, last 2
are the curve point's `(x, y)` coordinates. -/
def deserializeInput (input : Vector (Expression (F p)) inputLen)
    : Var Circuits.Endoscalar.GroupScale.Input (F p) :=
  { bits := Vector.ofFn (fun (i : Fin 128) =>
      input[i.val]'(by show i.val < 130; have := i.isLt; omega))
    pt := ⟨input[128]'(by show 128 < 130; omega), input[129]'(by show 129 < 130; omega)⟩ }

/-- Serialize the output point as a 2-wire vector. -/
def serializeOutput (output : Var Circuits.Point.Spec.Point (F p))
    : Vector (Expression (F p)) outputLen :=
  #v[output.x, output.y]

/-- `same_constraints` route: `CircuitFlattening.subcircuitWithHintAssertion_toFlat`
to peel the wrapper, then flatten — AddIncomplete (15) + Double (12) + the
`Circuit.foldl` of 64 `Step.circuit` subcircuits (36 ops each), exposed via
`Circuit.FoldlM.operations_eq` (cf. `CircuitFlattening.foldlRange_operations_eq`)
and the `*_toSubcircuit_toFlat` projection lemmas, closing with per-op `rfl`s
(the `Instances.NonzeroBank.ScopeK2` recipe, scaled up). Pending. -/
noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput
  deserializeInput
  serializeOutput
  reimplementation :=
    (Circuits.Endoscalar.GroupScale.circuit Circuits.Point.Spec.EpAffineParams).isGeneralFormalCircuit.toWithHint

  same_constraints := by sorry

  same_output := by sorry

end Ragu.Instances.Endoscalar.GroupScale
