import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- Under the `()` allocator, `Element::alloc` calls `Allocator::alloc`,
which emits a full 3-wire gate but returns the first wire — the other
two are discarded. The returned wire is unconstrained (there always
exist `b`, `c` satisfying `a · b = c` for any `a`, e.g. `b = c = 0`). -/
def main (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p)) (_ : Unit)
    : Circuit (F p) (Expression (F p)) := do
  let ⟨a, _, _⟩ ← Core.AllocMul.circuit hintReader ()
  return a

def Assumptions (_input : Unit) (_data : ProverData (F p)) (_hint : ProverHint (F p)) := True

/-- The output is unconstrained from the verifier's perspective — any value
can be part of a valid `(a, b, c)` triple with `a · b = c` (e.g. take
`a = c = 0`). The useful content is the allocation itself. -/
def Spec (_input : Unit) (_out : F p) (_data : ProverData (F p)) := True

instance elaborated (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : ElaboratedCircuit (F p) unit field where
  main := main hintReader
  localLength _ := 3

theorem soundness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) Spec := by
  circuit_proof_start

theorem completeness (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit.Completeness (F p) (elaborated hintReader) Assumptions := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions
  ]

def circuit (hintReader : ProverHint (F p) → Core.AllocMul.Row (F p))
    : GeneralFormalCircuit (F p) unit field :=
  { elaborated hintReader with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness hintReader,
    completeness := completeness hintReader }

end Ragu.Circuits.Element.Alloc
