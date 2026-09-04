import Clean.Circuit
import Ragu.Circuits.Point.Alloc
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Consistent
variable {p : ℕ} [Fact p.Prime]

/-- `Point::enforce_consistent` (`point.rs`):

```rust
Self::alloc(dr, self.value())?.enforce_conservative_equal(dr, self)
```

A fresh `Point::alloc` — the on-curve check — seeded from the existing
point's own coordinates, then linked to it coordinate by coordinate. The
hint is read off the input wires, as Rust reads `self.value()`, so the
circuit takes no separate hint. -/
def main (curveParams : Spec.CurveParams p) (input : Var Spec.Point (F p)) :
    Circuit (F p) (Var unit (F p)) := do
  let fresh ← Alloc.circuit curveParams fun env => ⟨env input.x, env input.y⟩
  assertZero (fresh.x - input.x)
  assertZero (fresh.y - input.y)

/-- No caller precondition: this is what *establishes* the point's contract. -/
def Assumptions (_input : Spec.Point (F p)) := True

/-- The existing point is on the curve and both coordinates are nonzero — the
full contract carried by Rust's `Point<Nonzero, Nonzero>` type. -/
def Spec (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) :=
  input.isOnCurve curveParams ∧ input.x ≠ 0 ∧ input.y ≠ 0

/-- One `Point::alloc`; the two links allocate nothing. -/
instance elaborated (curveParams : Spec.CurveParams p) :
    ElaboratedCircuit (F p) Spec.Point unit (main curveParams) where
  localLength _ := 9

/-- The fresh point is on the curve by `Alloc`'s spec, the links make it the
existing point, and the supported-curve facts rule out zero coordinates. -/
theorem soundness (curveParams : Spec.CurveParams p)
    (h_nonzero : curveParams.nonzeroCoordinates) :
    FormalAssertion.Soundness (F p) (Input := Spec.Point) (main curveParams)
      Assumptions (Spec curveParams) := by
  circuit_proof_start [Alloc.circuit, Alloc.Assumptions, Alloc.Spec]
  obtain ⟨h_curve, h_x, h_y⟩ := h_holds
  rw [sub_eq_zero] at h_x h_y
  have h_curve_input : (Spec.Point.mk input_x input_y).isOnCurve curveParams := by
    simp only [Spec.Point.isOnCurve] at h_curve ⊢
    rw [← h_x, ← h_y]
    exact h_curve
  exact ⟨h_curve_input, h_nonzero.1 ⟨input_x, input_y⟩ h_curve_input,
    h_nonzero.2 ⟨input_x, input_y⟩ h_curve_input⟩

/-- Seeding the fresh point from a point already on the curve reproduces it,
so both links hold; `Alloc`'s prover precondition is the spec. -/
theorem completeness (curveParams : Spec.CurveParams p) :
    FormalAssertion.Completeness (F p) (Input := Spec.Point) (main curveParams)
      Assumptions (Spec curveParams) := by
  circuit_proof_start [Alloc.circuit, Alloc.ProverAssumptions, Alloc.ProverSpec]
  obtain ⟨h_curve, _, _⟩ := h_spec
  obtain ⟨_, h_eq⟩ := h_env h_curve
  simp only [Spec.Point.mk.injEq] at h_eq
  obtain ⟨h_x, h_y⟩ := h_eq
  exact ⟨h_curve, by rw [h_x]; ring, by rw [h_y]; ring⟩

/-- `Point::enforce_consistent`. -/
def circuit (curveParams : Spec.CurveParams p) (h_nonzero : curveParams.nonzeroCoordinates) :
    FormalAssertion (F p) Spec.Point :=
  { main := main curveParams
    elaborated := elaborated curveParams
    Assumptions
    Spec := Spec curveParams
    soundness := soundness curveParams h_nonzero
    completeness := completeness curveParams }

end Ragu.Circuits.Point.Consistent
