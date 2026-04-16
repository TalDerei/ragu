import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

def main (hint : ProverData (F p) → F p) (_input : Unit) : Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let a := hint env.data
    (⟨a, a, a * a⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - y)
  return ⟨x, z⟩

def Assumptions (_hint : ProverData (F p) → F p) (_input : Unit) (_data : ProverData (F p)) := True

def Spec (_input : Unit) (out : Square (F p)) (_data : ProverData (F p)) :=
  out.a_sq = out.a^2

def CompletenessSpec (hint : ProverData (F p) → F p) (_input : Unit) (out : Square (F p)) (data : ProverData (F p)) :=
  out.a = hint data ∧ out.a_sq = (hint data)^2

instance elaborated (hint : ProverData (F p) → F p) : ElaboratedCircuit (F p) unit Square where
  main := main hint
  localLength _ := 3

theorem soundness (hint : ProverData (F p) → F p) : GeneralFormalCircuit.Soundness (F p) (elaborated hint) Spec := by
  circuit_proof_start
  obtain ⟨c1, c2⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2
  rw [←c1, c2]
  ring

theorem completeness (hint : ProverData (F p) → F p) : GeneralFormalCircuit.Completeness (F p) (elaborated hint) (Assumptions hint) := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  refine ⟨?_, ?_⟩ <;> ring

theorem completenessSpec (hint : ProverData (F p) → F p) : GeneralFormalCircuit.CompletenessSpecProof (F p) (elaborated hint) (Assumptions hint) (CompletenessSpec hint) := by
  circuit_proof_start [CompletenessSpec]
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero, Nat.reduceAdd, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  constructor
  · rw [h0]
  · rw [h2]; ring

def generalCircuit (hint : ProverData (F p) → F p) : GeneralFormalCircuit (F p) unit Square :=
  { elaborated hint with
    Assumptions := Assumptions hint,
    Spec := Spec,
    CompletenessSpec := CompletenessSpec hint,
    soundness := soundness hint,
    completeness := completeness hint,
    completenessSpec := completenessSpec hint }

end Ragu.Circuits.Element.AllocSquare
