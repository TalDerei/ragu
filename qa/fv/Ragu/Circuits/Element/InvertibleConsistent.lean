import Clean.Circuit
import Ragu.Circuits.Element.Invertible

namespace Ragu.Circuits.Element.InvertibleConsistent
variable {p : ℕ} [Fact p.Prime]

/-- `Invertible::enforce_consistent` (`invertible.rs`):

```rust
let value = D::just(|| *self.element.value().take());
let inverse_value = D::just(|| *self.inverse.value().take());
Self::alloc_with_advice(dr, value, inverse_value)?.enforce_conservative_equal(dr, self)
```

A fresh `Invertible::alloc_with_advice` seeded from the existing pair's own
values, then linked to it wire by wire. The link is the *conservative*
equality — `Invertible` derives `Gadget` over both `Nonzero` fields, so both
the element and the inverse are constrained equal, unlike the
`GadgetEquals` instance that compares elements alone. Both hints are read
off the input wires, as Rust reads `self.element.value()` and
`self.inverse.value()`, so the circuit takes no separate hint.

`Nonzero::enforce_consistent` is not a separate circuit: it is
`Element::enforce_invertible`, which `Element.EnforceInvertible` covers. -/
def main (input : Var Invertible.Pair (F p)) : Circuit (F p) (Var unit (F p)) := do
  let fresh ← Invertible.circuit fun env => ⟨env input.element, env input.inverse⟩
  assertZero (fresh.element - input.element)
  assertZero (fresh.inverse - input.inverse)

/-- No caller precondition: this is what *establishes* the pair's contract. -/
def Assumptions (_input : Invertible.Pair (F p)) := True

/-- The existing element is nonzero and the existing inverse really inverts
it — the contract `Invertible` carries in its type. -/
def Spec (input : Invertible.Pair (F p)) :=
  input.element ≠ 0 ∧ input.inverse = input.element⁻¹

/-- One `alloc_with_advice` gate; the two links allocate nothing. -/
instance elaborated : ElaboratedCircuit (F p) Invertible.Pair unit where
  main
  localLength _ := 3

/-- The fresh pair satisfies `Invertible`'s spec, and the links make it the
existing pair. -/
theorem soundness : FormalAssertion.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [Invertible.circuit, Invertible.Spec]
  obtain ⟨⟨h_ne, h_inv⟩, h_elem, h_inverse⟩ := h_holds
  rw [add_neg_eq_zero] at h_elem h_inverse
  rw [← h_elem, ← h_inverse]
  exact ⟨h_ne, h_inv⟩

/-- Seeding the fresh pair from a pair that already inverts reproduces it, so
both links hold; the advice condition `value · inverse = 1` is the spec. -/
theorem completeness : FormalAssertion.Completeness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [Invertible.circuit, Invertible.ProverAssumptions, Invertible.ProverSpec]
  obtain ⟨h_ne, h_inv⟩ := h_spec
  have h_one : input_element * input_inverse = 1 := by
    rw [h_inv]; exact mul_inv_cancel₀ h_ne
  obtain ⟨_, h_elem, h_inverse⟩ := h_env h_one
  exact ⟨h_one, by rw [h_elem]; ring, by rw [h_inverse]; ring⟩

/-- `Invertible::enforce_consistent`. -/
def circuit : FormalAssertion (F p) Invertible.Pair :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.InvertibleConsistent
