import Clean.Circuit
import Clean.Utils.Bits
import Ragu.Circuits.Boolean.Decompose

namespace Ragu.Circuits.Endoscalar.Extract
open Utils.Bits
variable {p : ℕ} [Fact p.Prime]

/-- `Endoscalar::extract` in its canonical-decomposition form: the challenge
element is decomposed into its `n = F::CAPACITY` little-endian bits and the
low 128 of them are the endoscalar. Mirrors `EndoscalarChallenge::from_element`
in `crates/ragu_primitives/src/endoscalar.rs` — every challenge constructor
(`sample` included) goes through it, and it is the only place constraints are
emitted; `Endoscalar::extract` itself just projects the bits out.

The Rust body is `Endoscalar::extract_element`: delegate to
`boolean.rs::decompose`, then keep the first 128 bits. The reimpl delegates
the same way — `Boolean.Decompose` emits every constraint, and this circuit
only projects — so the decomposition's canonicity argument lives with
`Decompose`. Taking 128 bits needs `128 ≤ n`, mirroring `extract_element`'s
`try_collect_fixed` over the first 128 decomposition bits.

The native range check in `from_element` (`try_just`) runs only during witness
generation and emits nothing, so it has no counterpart here;
`ProverAssumptions` carries it.

Extraction instance: `qa/lean/extraction/src/instances/endoscalar_extract.rs`
(drives the real gadget). Formal instance:
`qa/lean/Ragu/Instances/Endoscalar/Extract.lean` pins `n = 254`, the Pasta
capacity. -/
def main (n : ℕ) (h_cap : 2 ^ n < p) (h_len : 128 ≤ n) (input : Var field (F p))
    : Circuit (F p) (Var (fields 128) (F p)) := do
  let bits ← Boolean.Decompose.circuit n h_cap input
  return Vector.ofFn fun (i : Fin 128) => bits[i.val]'(by have := i.isLt; omega)

/-- Honest-prover precondition: the element is in range. An out-of-range
element has no `n`-bit decomposition — the case `from_element` rejects and
`EndoscalarChallenge::sample` resamples away. -/
def ProverAssumptions (n : ℕ) (input : F p) (_data : ProverData (F p))
    (_hint : ProverHint (F p)) :=
  input.val < 2 ^ n

/-- Verifier-side contract: any satisfying assignment places the element
below `2ⁿ`, and output wire `i` holds bit `i` of its canonical representative
(LSB first) — the endoscalar is the low 128 bits of the challenge. There is no
verifier-side precondition: the range restriction is enforced by the circuit,
not assumed. -/
def Spec (n : ℕ) (input : F p) (out : Vector (F p) 128) (_data : ProverData (F p)) :=
  input.val < 2 ^ n ∧ ∀ i : Fin 128, out[i] = if input.val.testBit i.val then 1 else 0

instance elaborated (n : ℕ) (h_cap : 2 ^ n < p) (h_len : 128 ≤ n)
    : ElaboratedCircuit (F p) field (fields 128) where
  main := main n h_cap h_len
  localLength _ := n * 3
  localLength_eq _ _ := by
    simp [main, circuit_norm, Boolean.Decompose.circuit]
  subcircuitsConsistent _ _ := by
    simp [main, circuit_norm, Boolean.Decompose.circuit]

theorem soundness (n : ℕ) (h_cap : 2 ^ n < p) (h_len : 128 ≤ n) :
    GeneralFormalCircuit.Soundness (F p) (elaborated n h_cap h_len) (fun _ _ => True) (Spec n) := by
  circuit_proof_start [Boolean.Decompose.circuit, Boolean.Decompose.Spec]
  obtain ⟨h_lt, h_bits⟩ := h_holds
  refine ⟨h_lt, fun i => ?_⟩
  have h_i := congrArg (fun v => v[i.val]'(by omega)) h_bits
  simp only [Vector.getElem_map, fieldToBits, toBits, Vector.getElem_mapRange] at h_i
  simpa [Vector.getElem_ofFn] using h_i

theorem completeness (n : ℕ) (h_cap : 2 ^ n < p) (h_len : 128 ≤ n) :
    GeneralFormalCircuit.Completeness (F p) (elaborated n h_cap h_len) (ProverAssumptions n)
      (fun _ _ _ => True) := by
  circuit_proof_start [Boolean.Decompose.circuit, Boolean.Decompose.Spec,
    Boolean.Decompose.ProverAssumptions]
  exact h_assumptions

def circuit (n : ℕ) (h_cap : 2 ^ n < p) (h_len : 128 ≤ n)
    : GeneralFormalCircuit (F p) field (fields 128) :=
  { elaborated n h_cap h_len with
    Spec := Spec n
    ProverAssumptions := ProverAssumptions n
    soundness := soundness n h_cap h_len
    completeness := completeness n h_cap h_len }

end Ragu.Circuits.Endoscalar.Extract
