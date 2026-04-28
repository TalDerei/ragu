import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- Under the `()` allocator, `Element::alloc` calls `Allocator::alloc`,
which emits a full 3-wire gate but returns the first wire — the other
two are discarded. The returned wire is unconstrained (there always
exist `b`, `c` satisfying `a · b = c` for any `a`, e.g. `b = c = 0`). -/
def main (hint : ProverEnvironment (F p) → Core.AllocMul.Row (F p))
    : Circuit (F p) (Expression (F p)) := do
  let ⟨a, _, _⟩ ← Core.AllocMul.circuit hint
  return a

def Assumptions (_input : Unit) (_data : ProverData (F p)) := True

def ProverAssumptions (_input : Core.AllocMul.Row (F p)) (_data : ProverData (F p))
    (_hint : ProverHint (F p)) := True

/-- The output is unconstrained from the verifier's perspective — any value
can be part of a valid `(a, b, c)` triple with `a · b = c` (e.g. take
`a = c = 0`). The useful content is the allocation itself. -/
def Spec (_input : Unit) (_out : F p) (_data : ProverData (F p)) := True

instance elaborated
    : ElaboratedCircuit (F p) (Unconstrained (Core.AllocMul.Row (F p))) field where
  main
  localLength _ := 3

theorem soundness
    : GeneralFormalCircuit.WithHint.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start

theorem completeness
    : GeneralFormalCircuit.WithHint.Completeness (F p) elaborated
        ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start [
    Core.AllocMul.circuit]

def circuit : GeneralFormalCircuit.WithHint (F p) (Unconstrained (Core.AllocMul.Row (F p))) field :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    ProverAssumptions := ProverAssumptions,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Element.Alloc
