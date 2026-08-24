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

/-- Verifier-side spec: the two returned wires multiply to one. That is the
whole content of the gadget — it implies both are nonzero, and it pins the
second wire as the first's inverse, which is what licenses `Invertible::invert`
to swap them without emitting anything. -/
def Spec (_input : Unit) (out : Pair (F p)) (_data : ProverData (F p)) :=
  out.element * out.inverse = 1

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
instance elaborated : ElaboratedCircuit (F p) (UnconstrainedDep Pair) Pair where
  main
  output _ offset := varFromOffset Pair offset
  localLength _ := 3

/-- The gate gives `a · b = c` and the assertion gives `c = 1`. -/
theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start
  obtain ⟨h_mul, h_c⟩ := h_holds
  rw [add_neg_eq_zero] at h_c
  rw [h_mul, h_c]

/-- The honest witness exists whenever the advice inverts the value, and it
puts the value and advice on the two returned wires. -/
theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) elaborated ProverAssumptions
      ProverSpec := by
  circuit_proof_start
  grind

/-- `Invertible::alloc_with_advice`, and by trace equality `Invertible::alloc`. -/
def circuit : GeneralFormalCircuit.WithHint (F p) (UnconstrainedDep Pair) Pair where
  elaborated
  Spec
  ProverAssumptions
  ProverSpec
  soundness
  completeness

/-- Nonzeroness of the element, the property callers actually quote. Kept as a
named lemma rather than folded into `Spec` because `Spec` must stay the
strongest statement the trace supports: `a · b = 1` pins the inverse too, and
`a ≠ 0` alone would lose that. -/
theorem element_ne_zero {out : Pair (F p)} (h : out.element * out.inverse = 1) :
    out.element ≠ 0 := by
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

end Ragu.Circuits.Element.Invertible
