import Clean.Circuit
import Ragu.Circuits.Element.Mul

namespace Ragu.Circuits.Poseidon.Sbox
variable {p : ℕ} [Fact p.Prime]

/-- `poseidon.rs::sbox` for `ALPHA = 5`: `x.square(dr)?.square(dr)?.mul(dr, x)?`,
three `Element::mul` gates in exactly that order, the last one linking its
second factor back to the original `x`. -/
def main (x : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  let x2 ← Element.Mul.circuit ⟨x, x⟩
  let x4 ← Element.Mul.circuit ⟨x2, x2⟩
  Element.Mul.circuit ⟨x4, x⟩

/-- No precondition: the fifth power is total. -/
def Assumptions (_x : F p) := True

/-- The output is the fifth power of the input. -/
def Spec (x : F p) (out : F p) := out = x ^ 5

/-- Three `Element.Mul` gates, nine wires; the result is the last gate's
product wire. -/
instance elaborated : ElaboratedCircuit (F p) field field main where
  output _ offset := varFromOffset field (offset + 8)
  localLength _ := 9

/-- Chaining the three multiplications gives `x^5`. -/
theorem soundness : Soundness (F p) (Input := field) (Output := field) main Assumptions Spec := by
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec]
  obtain ⟨h2, h4, h5⟩ := h_holds
  rw [h5, h4, h2]
  ring

/-- Every `Element.Mul` is total, so the honest witness always exists. -/
theorem completeness : Completeness (F p) (Input := field) (Output := field) main Assumptions := by
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions]

/-- The Poseidon S-box `x ↦ x^5` for `ALPHA = 5`. -/
def circuit : FormalCircuit (F p) field field :=
  { main := main, elaborated := elaborated, Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Poseidon.Sbox
