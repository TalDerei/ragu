import Ragu.Circuits.Endoscalar.GroupScale
import Ragu.Circuits.Point.AddIncomplete
import Ragu.Circuits.Point.ConditionalEndo
import Ragu.Circuits.Point.ConditionalNegate
import Ragu.Circuits.Point.Double
import Ragu.Circuits.Point.DoubleAndAddIncomplete
import Ragu.Circuits.Point.Spec
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.DivNonzero
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Core.Mul
import Ragu.Instances.Autogen.Endoscalar.GroupScale
import Ragu.Core
import Mathlib.Tactic.IntervalCases

namespace Ragu.Instances.Endoscalar.GroupScale
open Ragu.Instances.Autogen.Endoscalar.GroupScale

set_option maxHeartbeats 4000000000
set_option maxRecDepth 1000000

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

/-- The byte-equivalence proof for `same_constraints` requires inducting on
the 64-iteration `Vector.foldlM` and decomposing each iteration's 36-wire
constraint block: ConditionalNegate (3) + ConditionalEndo (3) +
DoubleAndAddIncomplete (24, including its internal bank folds and
`enforce_nonzero` discharge) + two freshening `Element.Mul`s (3 + 3). The
full proof follows the pattern in `Endoscalar.Lift`'s `mapM_boolean_and_ops`
lemma. Pending lake iteration. -/
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
