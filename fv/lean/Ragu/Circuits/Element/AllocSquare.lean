import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

def main (idx : ℕ) (_input : Unit) : Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env => Core.AllocMul.readRow env.data idx
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - y)
  return ⟨x, z⟩

def Assumptions (idx : ℕ) (_input : Unit) (data : ProverData (F p)) :=
  let w := Core.AllocMul.readRow data idx
  w.x = w.y ∧ w.x * w.y = w.z

def Spec (_input : Unit) (out : Square (F p)) (_data : ProverData (F p)) :=
  out.a_sq = out.a^2

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) unit Square where
  main := main idx
  localLength _ := 3

theorem soundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) Spec := by
  circuit_proof_start
  obtain ⟨c1, c2⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2
  rw [←c1, c2]
  ring

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
  obtain ⟨h_eq, h_mul⟩ := h_assumptions
  constructor
  · rw [add_neg_eq_zero]; convert h_mul using 2 <;> simp
  · rw [add_neg_eq_zero]; convert h_eq using 2 <;> simp

def circuit (idx : ℕ) : GeneralFormalCircuit (F p) unit Square :=
  { elaborated idx with Assumptions := Assumptions idx, Spec, soundness := soundness idx, completeness := completeness idx }

end Ragu.Circuits.Element.AllocSquare
