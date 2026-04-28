import Clean.Circuit

namespace Ragu.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

def main (hint : ProverEnvironment (F p) → Row (F p)) : Circuit (F p) (Var Row (F p)) := do
  let row : Var Row (F p) ← witness fun env =>
    let ⟨ x, y, _ ⟩ := hint env
    ⟨ x, y, x * y⟩
  assertZero (row.x * row.y - row.z)
  return row

def Spec (_input : Unit) (out : Row (F p)) (_data : ProverData (F p)) :=
  out.x * out.y = out.z

/-- The output row equals `hintReader` applied to the runtime hint. -/
def ProverSpec (input : Row (F p)) (out : Row (F p)) (_ : ProverHint (F p)) :=
  let ⟨ x, y, _ ⟩ := input
  out.x = x ∧ out.y = y ∧ out.z = x * y

instance elaborated : ElaboratedCircuit (F p) (Unconstrained (Row (F p))) Row where
  main
  localLength _ := 3

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start [Spec]
  simp only [add_neg_eq_zero] at h_holds
  exact h_holds

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) elaborated (fun _ _ _ => True) ProverSpec := by
  circuit_proof_start [ProverSpec]
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  simp at h0 h1 h2
  constructor
  · rw [h0, h1, h2]
    ring_nf
  · exact ⟨h0, h1, h2⟩

def circuit : GeneralFormalCircuit.WithHint (F p) (Unconstrained (Row (F p))) Row where
  elaborated
  Spec
  ProverSpec
  soundness
  completeness

end Circuits.Core.AllocMul
export Circuits.Core.AllocMul (Row)
end Ragu
