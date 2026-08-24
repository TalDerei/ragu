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

/-- The existing point is on the curve — the contract `Point` carries in its
type. -/
def Spec (curveParams : Spec.CurveParams p) (input : Spec.Point (F p)) :=
  input.isOnCurve curveParams

/-- One `Point::alloc`; the two links allocate nothing. -/
instance elaborated (curveParams : Spec.CurveParams p) :
    ElaboratedCircuit (F p) Spec.Point unit where
  main := main curveParams
  localLength _ := 9

/-- The fresh point is on the curve by `Alloc`'s spec, and the links make it
the existing point. -/
theorem soundness (curveParams : Spec.CurveParams p) :
    FormalAssertion.Soundness (F p) (elaborated curveParams) Assumptions (Spec curveParams) := by
  circuit_proof_start [Alloc.circuit, Alloc.Assumptions, Alloc.Spec]
  obtain ⟨h_curve, h_x, h_y⟩ := h_holds
  rw [add_neg_eq_zero] at h_x h_y
  simp only [Spec.Point.isOnCurve] at h_curve ⊢
  rw [← h_x, ← h_y]
  exact h_curve

/-- Seeding the fresh point from a point already on the curve reproduces it,
so both links hold; `Alloc`'s prover precondition is the spec. -/
theorem completeness (curveParams : Spec.CurveParams p) :
    FormalAssertion.Completeness (F p) (elaborated curveParams) Assumptions (Spec curveParams) := by
  circuit_proof_start [Alloc.circuit, Alloc.ProverAssumptions, Alloc.ProverSpec]
  obtain ⟨_, h_eq⟩ := h_env h_spec
  simp only [Spec.Point.mk.injEq] at h_eq
  obtain ⟨h_x, h_y⟩ := h_eq
  exact ⟨h_spec, by rw [h_x]; ring, by rw [h_y]; ring⟩

/-- `Point::enforce_consistent`. -/
def circuit (curveParams : Spec.CurveParams p) : FormalAssertion (F p) Spec.Point :=
  { elaborated curveParams with
    Assumptions
    Spec := Spec curveParams
    soundness := soundness curveParams
    completeness := completeness curveParams }

end Ragu.Circuits.Point.Consistent
