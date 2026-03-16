import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.Mul
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

def main (idx : ℕ) (input : Var Input (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env => Core.AllocMul.readRow env.data idx
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - input.x)
  assertZero (y - input.y)
  return z

def Assumptions (idx : ℕ) (input : Input (F p)) (data : ProverData (F p)) :=
  let w := Core.AllocMul.readRow data idx
  w.x = input.x ∧ w.y = input.y ∧ w.x * w.y = w.z

def Spec (input : Input (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  out = input.x * input.y

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) Input field where
  main := main idx
  localLength _ := 3

theorem soundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c3
  rw [←c2, ←c3, c1]

theorem completeness (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (Assumptions idx) := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, Core.AllocMul.readRow, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  simp only [Core.AllocMul.readRow] at h_assumptions
  obtain ⟨h_wx, h_wy, h_mul⟩ := h_assumptions
  constructor
  · rw [add_neg_eq_zero]; convert h_mul using 2 <;> simp
  constructor
  · rw [add_neg_eq_zero]; convert h_wx using 2 <;> simp
  · rw [add_neg_eq_zero]; convert h_wy using 2 <;> simp

def circuit (idx : ℕ) : GeneralFormalCircuit (F p) Input field :=
  {
    elaborated idx with
    Assumptions := Assumptions idx,
    Spec,
    soundness := soundness idx,
    completeness := completeness idx
  }

end Ragu.Circuits.Element.Mul
