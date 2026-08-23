import Clean.Circuit
import Ragu.Circuits.Element.InvertWith

namespace Ragu.Circuits.Element.Invert
variable {p : ℕ} [Fact p.Prime]

/-- `Element::invert(input)` delegates to `invert_with` with an inverse
witness derived from the input. The Lean reimpl mirrors that delegation
directly via the `InvertWith` subcircuit; the only added obligation is
the caller's `input ≠ 0` (otherwise the inverse doesn't exist and the
honest prover can't satisfy `b · input = 1`). -/
def main (input : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  InvertWith.circuit { input, inverse env := (env input)⁻¹ }

def ProverAssumptions (input : F p) (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  input ≠ 0

def Spec (input : F p) (out : F p) (_data : ProverData (F p)) :=
  input * out = 1

instance elaborated : ElaboratedCircuit (F p) field field where
  main
  output _ offset := varFromOffset field (offset + 1)
  localLength _ := 3

theorem soundness
    : GeneralFormalCircuit.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start [InvertWith.circuit, InvertWith.Spec]
  exact h_holds

theorem completeness
    : GeneralFormalCircuit.Completeness (F p) elaborated
        ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start [InvertWith.circuit, InvertWith.ProverAssumptions]
  exact mul_inv_cancel₀ h_assumptions

def circuit : GeneralFormalCircuit (F p) field field :=
  { elaborated with Spec, ProverAssumptions, soundness, completeness }

end Ragu.Circuits.Element.Invert
