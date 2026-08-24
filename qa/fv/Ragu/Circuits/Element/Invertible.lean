import Clean.Circuit
import Ragu.Circuits.Core.Mul

namespace Ragu.Circuits.Element.Invertible
variable {p : ℕ} [Fact p.Prime]

/-- The pair of wires an `Invertible` gadget carries: the element and its
multiplicative inverse. Rust stores both (`Invertible { element, inverse }`),
which is what makes `Invertible::invert` free — it swaps the two fields and
emits nothing. -/
structure Pair (F : Type) where
  /-- The allocated element, the mul gate's first wire. -/
  element : F
  /-- Its multiplicative inverse, the mul gate's second wire. -/
  inverse : F
deriving ProvableStruct

/-- `Invertible::alloc_with_advice` (`invertible.rs`): one mul gate
`(a, b, c)` with the value and its inverse as witness input, followed by
`enforce_equal(c, ONE)`. Both wires are returned.

`Invertible::alloc` has the same trace — it only computes the inverse
witness before delegating here, and witness bodies are not executed under
extraction — so this circuit covers both entry points.

Unlike `Element.EnforceNonzero`, no constraint links `a` to a pre-existing
wire: this is an *allocation*, so the element it constrains nonzero is the
one it just created. `Element.EnforceInvertible` is the linked variant.

Both wires are outputs. `Invertible` derives `Gadget` over its two `Nonzero`
fields, and the extractor collects a gadget's wires, so the trace carries
`(a, b)` — not the one-wire `Write` encoding, which is a separate
serialization used elsewhere and omits the derivable inverse. -/
def main (hint : ProverEnvironment (F p) → Pair (F p)) :
    Circuit (F p) (Var Pair (F p)) := do
  let ⟨a, b, c⟩ ← Core.mul fun env =>
    let ⟨value, inverse⟩ := hint env
    ⟨value, inverse, 1⟩
  assertZero (c - 1)
  return ⟨a, b⟩

/-- Verifier-side spec: the allocated element is nonzero and the second wire
really is its multiplicative inverse. Stated this way rather than as the
emitted equation `element · inverse = 1` because it is what callers reason
against: `Nonzero`'s type invariant is the first conjunct, and the second is
what licenses `Invertible::invert` to swap the two fields and emit nothing. -/
def Spec (_input : Unit) (out : Pair (F p)) (_data : ProverData (F p)) :=
  out.element ≠ 0 ∧ out.inverse = out.element⁻¹

/-- Prover-side assumption: the supplied advice really is the inverse, so the
prover can satisfy `a · b = 1`. This is exactly Rust's documented completeness
condition ("witness generation succeeds when `value` is nonzero and
`inverse_value` matches its inverse"). -/
def ProverAssumptions (input : ProverValue Pair (F p))
    (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  let value : F p := input.element
  let inverse : F p := input.inverse
  value * inverse = 1

/-- Prover-side output spec: the honest witness puts the value and its advice
on the two returned wires, in that order. Callers that link one of these wires
to a wire of their own — `Element.EnforceInvertible` does exactly that — need
this to discharge the link during their own completeness proof; `Spec` alone
pins only the product. -/
def ProverSpec (input : ProverValue Pair (F p)) (out : Pair (F p))
    (_hint : ProverHint (F p)) :=
  let value : F p := input.element
  let inverse : F p := input.inverse
  out.element = value ∧ out.inverse = inverse

/-- One mul gate: three wires, of which the first two are the output pair. -/
instance elaborated : ElaboratedCircuit (F p) (UnconstrainedDepNative Pair) Pair main where
  output _ offset := varFromOffset Pair offset
  localLength _ := 3

/-- The gate gives `a · b = c` and the assertion gives `c = 1`; a product of
one makes the first factor nonzero and the second its inverse. -/
theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) (Input := (UnconstrainedDepNative Pair))
      (Output := Pair) main (fun _ _ => True) Spec := by
  circuit_proof_start
  obtain ⟨h_mul, h_c⟩ := h_holds
  rw [sub_eq_zero] at h_c
  have h1 : env.get i₀ * env.get (i₀ + 1) = 1 := by rw [h_mul, h_c]
  refine ⟨?_, ?_⟩
  · intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)

/-- The honest witness exists whenever the advice inverts the value, and it
puts the value and advice on the two returned wires. -/
theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) (Input := (UnconstrainedDepNative Pair))
      (Output := Pair) main ProverAssumptions ProverSpec := by
  circuit_proof_start
  grind

/-- `Invertible::alloc_with_advice`, and by trace equality `Invertible::alloc`. -/
def circuit : GeneralFormalCircuit.WithHint (F p) (UnconstrainedDepNative Pair) Pair where
  main
  elaborated := elaborated
  Spec
  ProverAssumptions
  ProverSpec
  soundness
  completeness

end Ragu.Circuits.Element.Invertible
