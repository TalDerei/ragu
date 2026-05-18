import Clean.Circuit
import Clean.Circuit.Loops
import Ragu.Circuits.Boolean.Alloc

namespace Ragu.Circuits.Endoscalar.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- `Endoscalar::alloc(value)` allocates 128 boolean wires, each carrying
the corresponding bit of the 128-bit prover hint `value`. Mirrors the
Rust loop `for i in 0..Uendo::BITS { Boolean::alloc((value >> i) & 1) }`
in `crates/ragu_primitives/src/endoscalar.rs::Endoscalar::alloc`.

`Uendo` is `pub use u128 as Uendo` in `crates/ragu_arithmetic/src/lib.rs:102`,
so `Uendo::BITS = u128::BITS = 128`. This Lean reimpl is monomorphic at 128 —
no polymorphism needed.

TODO: extraction instance deferred. The 512-operation autogen (128 Booleans ×
4 ops each) exceeds what Clean's current simp/tactic infrastructure can reduce
through a `Circuit.mapFinRange`-based `main` to match the extractor's literal
operation list. Per fv-review's sub-gadget carve-out, this is acceptable
because `Endoscalar::alloc` is only called from other circuit factories
(`internal/endoscalar.rs`, `staging/mask.rs`) — trust flows through their
extraction instances when ported. Revisit once Clean exposes an
`operations_eq` lemma for `mapFinRange` suitable for unfolding at concrete `n`. -/
def main (value : ProverEnvironment (F p) → BitVec 128)
    : Circuit (F p) (Vector (Expression (F p)) 128) :=
  Circuit.mapFinRange 128 fun (i : Fin 128) =>
    Boolean.Alloc.circuit (fun env => (value env)[i.val])

def Assumptions (_input : Unit) (_data : ProverData (F p)) := True

def ProverAssumptions (_input : BitVec 128) (_data : ProverData (F p))
    (_hint : ProverHint (F p)) := True

/-- The verifier learns that all 128 output wires are boolean. -/
def Spec (_input : Unit) (out : Vector (F p) 128) (_data : ProverData (F p)) :=
  ∀ i : Fin 128, IsBool out[i]

instance elaborated
    : ElaboratedCircuit (F p) (Unconstrained (BitVec 128)) (fields 128) where
  main
  localLength _ := 128 * 3
  localLength_eq _ _ := by
    simp [main, circuit_norm, Boolean.Alloc.circuit]
  subcircuitsConsistent _ _ := by
    simp [main, circuit_norm, Boolean.Alloc.circuit]

theorem soundness
    : GeneralFormalCircuit.WithHint.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [Boolean.Alloc.circuit, Boolean.Alloc.Assumptions, Boolean.Alloc.Spec]
  exact h_holds

theorem completeness
    : GeneralFormalCircuit.WithHint.Completeness (F p) elaborated
        ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start [Boolean.Alloc.circuit, Boolean.Alloc.Assumptions, Boolean.Alloc.Spec,
    Boolean.Alloc.ProverAssumptions]

def circuit : GeneralFormalCircuit.WithHint (F p) (Unconstrained (BitVec 128)) (fields 128) :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    ProverAssumptions := ProverAssumptions,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Endoscalar.Alloc
