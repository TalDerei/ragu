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

def Assumptions (_x : F p) := True

def Spec (x : F p) (out : F p) := out = x ^ 5

instance elaborated : ElaboratedCircuit (F p) field field where
  main
  output _ offset := varFromOffset field (offset + 8)
  localLength _ := 9

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec]
  obtain ⟨h2, h4, h5⟩ := h_holds
  rw [h5, h4, h2]
  ring

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [Element.Mul.circuit, Element.Mul.Assumptions]

def circuit : FormalCircuit (F p) field field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Poseidon.Sbox
