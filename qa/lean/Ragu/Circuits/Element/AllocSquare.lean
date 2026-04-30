import Clean.Circuit
import Ragu.Circuits.Core.Mul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

def main (hint : ProverEnvironment (F p) → F p) :
    Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← Core.mul fun env =>
    let a := hint env
    ⟨a, a, a * a⟩
  assertZero (x - y)
  return ⟨x, z⟩

def Spec (_input : Unit) (out : Square (F p)) (_data : ProverData (F p)) :=
  out.a_sq = out.a^2

def ProverSpec (input : F p) (out : Square (F p)) (_hint : ProverHint (F p)) :=
  out.a = input ∧ out.a_sq = input^2

instance elaborated :
    ElaboratedCircuit (F p) (UnconstrainedDep field) Square where
  main
  output _ offset := { a := varFromOffset field offset, a_sq := varFromOffset field (offset + 2) }
  localLength _ := 3

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start
  obtain ⟨h_mul, h_eq⟩ := h_holds
  -- h_mul : x * y = z, h_eq : x - y = 0
  rw [add_neg_eq_zero] at h_eq
  -- Goal: z = x^2
  rw [← h_mul, h_eq]; ring

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) elaborated
      (fun _ _ _ => True) ProverSpec := by
  circuit_proof_start
  grind

def circuit : GeneralFormalCircuit.WithHint (F p) (UnconstrainedDep field) Square :=
  { elaborated with Spec, ProverSpec, soundness, completeness }

end Ragu.Circuits.Element.AllocSquare
