import Clean.Circuit
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Element.Fold
variable {p : ℕ} [Fact p.Prime]

/-- `Element::fold` is variadic (`IntoIterator<Element>`). This extraction
instance fixes length 3 as a representative choice. The scale factor is
itself an `Element` in production — an input wire, not a compile-time
parameter — so it appears in `Input`. -/
structure Input (F : Type) where
  x0 : F
  x1 : F
  x2 : F
  s : F  -- scale factor
deriving ProvableStruct

/-- Horner fold: `((x0 · s) + x1) · s + x2 = x0·s² + x1·s + x2`. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  let acc0_s ← subcircuit Mul.circuit ⟨input.x0, input.s⟩
  let acc1 := acc0_s + input.x1
  let acc1_s ← subcircuit Mul.circuit ⟨acc1, input.s⟩
  return acc1_s + input.x2

def Assumptions (_input : Input (F p)) := True

def Spec (input : Input (F p)) (output : F p) :=
  output = (input.x0 * input.s + input.x1) * input.s + input.x2

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 6

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp [circuit_norm, Mul.circuit, Mul.Assumptions, Mul.Spec] at h_holds ⊢
  obtain ⟨h1, h2⟩ := h_holds
  -- h1: first mul output = x0 * s
  -- h2: second mul output = (first mul output + x1) * s
  rw [h1] at h2
  rw [h2]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [Mul.circuit, Mul.Assumptions]

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.Fold
