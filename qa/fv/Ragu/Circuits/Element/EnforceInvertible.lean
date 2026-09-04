import Clean.Circuit
import Ragu.Core
import Ragu.Circuits.Element.Invertible

namespace Ragu.Circuits.Element.EnforceInvertible
variable {p : ℕ} [Fact p.Prime]

/-- `Input` carries the element to be constrained invertible, plus a
prover-side hint with its multiplicative inverse. -/
structure Input (F : Type) where
  /-- The element the caller already holds a wire for. -/
  element : F
  /-- Prover hint: its multiplicative inverse. -/
  inverse : UnconstrainedDep field F
deriving CircuitType

/-- `Element::enforce_invertible_with` (`element.rs`):

```rust
let invertible = Invertible::alloc_with_advice(dr, self.value.clone(), inverse_value)?;
self.enforce_equal(dr, invertible.element())?;
Ok(invertible)
```

The reimplementation mirrors that delegation: the boxed
`Element.Invertible` sub-gadget allocates the `(a, b)` pair and constrains
`a · b = 1`, then one linear constraint links `a` to the caller's wire.

`Element::enforce_invertible` has the same trace — it differs only in
computing the inverse witness itself, and witness bodies are not executed
under extraction — so this circuit covers both entry points.

The *operations* coincide with `Element.EnforceNonzero`'s, because Rust's
`enforce_nonzero` is literally `enforce_invertible(...).into_element()`. The
traces still differ, and so do the fingerprints: `Nonzero` carries one wire,
`Invertible` carries two, so this instance collects `(a, b)` where
`EnforceNonzero` collects `a` alone. That difference is the point — it is
what pins the second gate wire as the inverse, which is what licenses
`Invertible::invert` to swap the two fields and emit nothing. -/
def main (input : Var Input (F p)) : Circuit (F p) (Var Invertible.Pair (F p)) := do
  let ⟨x, inverse⟩ := input
  let pair ← Invertible.circuit fun env => ⟨env x, inverse env⟩
  assertZero (x - pair.element)
  return pair

/-- Verifier-side spec: the returned element is the caller's wire, that wire is
nonzero, and the returned inverse really inverts it. The nonzeroness is the
point of the gadget — it is what `Nonzero` and `Invertible` encode in their
types — so it is stated here rather than left implicit in a product. -/
def Spec (input : Value Input (F p))
    (out : Invertible.Pair (F p)) (_data : ProverData (F p)) :=
  out.element = input.element ∧ out.element ≠ 0 ∧ out.inverse = out.element⁻¹

/-- Prover-side assumption: the hint really inverts the element. -/
def ProverAssumptions (input : ProverValue Input (F p))
    (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  let element : F p := input.element
  let inverse : F p := input.inverse
  element * inverse = 1

/-- One mul gate from the sub-gadget; the link is a linear constraint and
allocates nothing. -/
instance elaborated : ElaboratedCircuit (F p) Input Invertible.Pair where
  main
  output _ offset := varFromOffset Invertible.Pair offset
  localLength _ := 3

/-- The sub-gadget gives `a · b = 1`; the link gives `a = x`. -/
theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start [Invertible.circuit, Invertible.Spec]
  obtain ⟨h_pair, h_link⟩ := h_holds
  rw [add_neg_eq_zero] at h_link
  exact ⟨h_link.symm, h_pair⟩

/-- The sub-gadget is complete under the same hint condition, and the link
holds by construction. -/
theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) elaborated ProverAssumptions
      (fun _ _ _ => True) := by
  circuit_proof_start [Invertible.circuit, Invertible.ProverAssumptions, Invertible.ProverSpec]
  grind

/-- `Element::enforce_invertible_with`, and by trace equality
`Element::enforce_invertible`. -/
def circuit : GeneralFormalCircuit.WithHint (F p) Input Invertible.Pair where
  elaborated
  Spec
  ProverAssumptions
  soundness
  completeness

end Ragu.Circuits.Element.EnforceInvertible
