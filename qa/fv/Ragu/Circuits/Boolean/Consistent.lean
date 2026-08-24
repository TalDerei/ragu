import Clean.Circuit
import Clean.Gadgets.Boolean
import Ragu.Circuits.Boolean.Alloc

namespace Ragu.Circuits.Boolean.Consistent
variable {p : ℕ} [Fact p.Prime]

/-- `Boolean::enforce_consistent` (`boolean.rs`):

```rust
Self::alloc(dr, &mut (), self.value())?.enforce_conservative_equal(dr, self)
```

The `Consistent` trait exists for the staging machinery, which substitutes a
gadget's wires into a context where the constraints that made them a gadget
were never emitted; `enforce_consistent` re-emits those constraints on the
wires as they are. For a boolean that is a fresh `Boolean::alloc` seeded
from the existing wire's own value, linked to it by one equality. The hint
is computed from the input wire, exactly as Rust reads `self.value()`, so
the circuit takes no separate hint. -/
def main (x : Expression (F p)) : Circuit (F p) (Var unit (F p)) := do
  let fresh ← Alloc.circuit fun env => decide (env x = 1)
  assertZero (fresh - x)

/-- No caller precondition: this is what *establishes* the wire's contract. -/
def Assumptions (_x : F p) := True

/-- The existing wire is boolean — the contract `Boolean` carries in its
type, re-established here on a wire that arrived without it. -/
def Spec (x : F p) := IsBool x

/-- One `Boolean::alloc` gate; the link allocates nothing. -/
instance elaborated : ElaboratedCircuit (F p) field unit main where
  localLength _ := 3

/-- The fresh wire is boolean by `Alloc`'s spec, and the link makes it the
existing wire. -/
theorem soundness :
    FormalAssertion.Soundness (F p) (Input := field) main Assumptions Spec := by
  circuit_proof_start [Alloc.circuit, Alloc.Assumptions, Alloc.Spec]
  obtain ⟨h_bool, h_link⟩ := h_holds
  rw [sub_eq_zero] at h_link
  rw [← h_link]
  exact h_bool

/-- Seeding the fresh boolean from a wire that is already boolean reproduces
that wire, so the link holds. -/
theorem completeness :
    FormalAssertion.Completeness (F p) (Input := field) main Assumptions Spec := by
  circuit_proof_start [Alloc.circuit, Alloc.ProverAssumptions, Alloc.ProverSpec]
  obtain ⟨_, h_fresh⟩ := h_env
  rw [h_fresh]
  rcases h_spec with h | h <;> simp [h]

/-- `Boolean::enforce_consistent`. -/
def circuit : FormalAssertion (F p) field :=
  { main, elaborated := elaborated, Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Boolean.Consistent
