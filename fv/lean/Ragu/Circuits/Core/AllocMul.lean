import Clean.Circuit

namespace Ragu.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

def main (hint : ProverData (F p) → Row (F p)) (_input : Unit) : Circuit (F p) (Var Row (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let r := hint env.data
    (⟨r.x, r.y, r.x * r.y⟩ : Row (F p))
    : Circuit (F p) (Var Row (F p)))
  assertZero (x * y - z)
  return ⟨x, y, z⟩

def Assumptions (_hint : ProverData (F p) → Row (F p)) (_input : Unit) (_data : ProverData (F p)) := True

def Spec (_input : Unit) (out : Row (F p)) (_data : ProverData (F p)) :=
  out.x * out.y = out.z

/-- The output row matches the hint on `x`/`y`; `z` is always wired to `x * y`. -/
def CompletenessSpec (hint : ProverData (F p) → Row (F p)) (_input : Unit) (out : Row (F p)) (data : ProverData (F p)) :=
  let r := hint data
  out.x = r.x ∧ out.y = r.y ∧ out.z = r.x * r.y

instance elaborated (hint : ProverData (F p) → Row (F p)) : ElaboratedCircuit (F p) unit Row where
  main := main hint
  localLength _ := 3

theorem soundness (hint : ProverData (F p) → Row (F p)) : GeneralFormalCircuit.Soundness (F p) (elaborated hint) (Spec) := by
  circuit_proof_start
  rw [add_neg_eq_zero] at h_holds
  exact h_holds

theorem completeness (hint : ProverData (F p) → Row (F p)) : GeneralFormalCircuit.Completeness (F p) (elaborated hint) (Assumptions hint) := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  ring

theorem completenessSpec (hint : ProverData (F p) → Row (F p)) : GeneralFormalCircuit.CompletenessSpecProof (F p) (elaborated hint) (Assumptions hint) (CompletenessSpec hint) := by
  circuit_proof_start [CompletenessSpec]
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  simp

def circuit (hint : ProverData (F p) → Row (F p)) : GeneralFormalCircuit (F p) unit Row :=
  { elaborated hint with
    Assumptions := Assumptions hint,
    Spec := Spec,
    CompletenessSpec := CompletenessSpec hint,
    soundness := soundness hint,
    completeness := completeness hint,
    completenessSpec := completenessSpec hint }

end Ragu.Circuits.Core.AllocMul
