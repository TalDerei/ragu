import Clean.Circuit
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Element.Square
variable {p : ℕ} [Fact p.Prime]

-- TODO: this is not necessary, there is `field`, but currently it's hard to
-- work with, because Lean sometimes thinks `field T` and `T` are definitionally
-- equivalent, (`field` is definitionally equal to `id`) and sometimes not
structure Element (F : Type) where
  wire : F
deriving ProvableStruct

def main (idx : ℕ) (input : Var Element (F p)) : Circuit (F p) (Var Element (F p)) := do
  let ⟨x⟩ := input
  return {
    wire := ←Mul.circuit idx ⟨x, x⟩
  }

def Assumptions (idx : ℕ) (_input : Element (F p)) (data : ProverData (F p)) :=
  Mul.Assumptions idx ⟨_input.wire, _input.wire⟩ data

def Spec (input : Element (F p)) (out : Element (F p)) (_data : ProverData (F p)) :=
  out.wire = input.wire^2

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) Element Element where
  main := main idx
  localLength _ := 3

theorem soundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) Spec := by
  circuit_proof_start
  simp [circuit_norm, Mul.circuit, Mul.Spec] at h_holds ⊢
  rw [h_holds]
  ring

theorem completeness (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (Assumptions idx) := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions]
  exact h_assumptions

def circuit (idx : ℕ) : GeneralFormalCircuit (F p) Element Element :=
  { elaborated idx with Assumptions := Assumptions idx, Spec, soundness := soundness idx, completeness := completeness idx }

end Ragu.Circuits.Element.Square
