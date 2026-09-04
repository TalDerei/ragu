import Clean.Circuit

namespace Ragu.Circuits
/-- A single R1CS row, used in the constraint x * y = z -/
structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

namespace Core.Mul
variable {p : ℕ} [Fact p.Prime]

def main (hint : ProverEnvironment (F p) → Row (F p)) : Circuit (F p) (Var Row (F p)) := do
  let row : Var Row (F p) ← witness fun env =>
    let ⟨ x, y, _ ⟩ := hint env
    ⟨ x, y, x * y⟩
  assertZero (row.x * row.y - row.z)
  return row

/-- We add this spec to the simp set since many gadgets rely on it -/
@[circuit_norm]
def Spec (_input : Unit) (out : Row (F p)) (_data : ProverData (F p)) :=
  out.x * out.y = out.z

/-- The output row equals `hintReader` applied to the runtime hint.
We add this to the simp set since many gadgets rely on it -/
@[circuit_norm]
def ProverSpec (input : Row (F p)) (out : Row (F p)) (_ : ProverHint (F p)) :=
  let ⟨ x, y, _ ⟩ := input
  out.x = x ∧ out.y = y ∧ out.z = x * y

@[circuit_norm]
instance elaborated : ElaboratedCircuit (F p) (UnconstrainedDep Row) Row where
  main
  output _ offset := varFromOffset Row offset
  localLength _ := 3

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start
  simp only [add_neg_eq_zero] at h_holds
  exact h_holds

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) elaborated (fun _ _ _ => True) ProverSpec := by
  circuit_proof_start
  -- TODO this is annoying, we need simp for ProvableStruct.toElements
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm] at h0 h1 h2
  simp at h0 h1 h2
  simp [h0, h1, h2]

@[circuit_norm]
def mul : GeneralFormalCircuit.WithHint (F p) (UnconstrainedDep Row) Row where
  elaborated
  Spec
  ProverSpec
  soundness
  completeness
end Mul

-- export as `Core.mul` for use in other circuits
export Mul (mul)
end Ragu.Circuits.Core
