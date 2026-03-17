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

def main (input : Var Element (F p)) : Circuit (F p) (Var Element (F p)) := do
  let ⟨x⟩ := input
  return {
    wire := ←Mul.circuit ⟨x, x⟩
  }

def Assumptions (_input : Element (F p)) :=
  True

def Spec (input : Element (F p)) (out : Element (F p)) :=
  out.wire = input.wire^2

instance elaborated : ElaboratedCircuit (F p) Element Element where
  main := main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp [circuit_norm, Mul.circuit, Mul.Spec, Mul.Assumptions] at h_holds ⊢
  rw [h_holds]
  ring

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions]

def circuit : FormalCircuit (F p) Element Element :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Square
