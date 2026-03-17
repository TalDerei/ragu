import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct

-- w maps as: (quotient, denominator, numerator) i.e. quotient * denominator = numerator
def main (input : Var Inputs (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨quotient, denominator, numerator⟩ ← (witness fun env =>
    let xv := Expression.eval env input.x
    let yv := Expression.eval env input.y
    ⟨xv / yv, yv, xv⟩
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (quotient * denominator - numerator)

  assertZero (input.x - numerator)
  assertZero (input.y - denominator)

  return quotient

def Assumptions (input : Inputs (F p)) :=
  input.y ≠ 0

def Spec (input : Inputs (F p)) (out : field (F p)) :=
  out = input.x / input.y

instance elaborated : ElaboratedCircuit (F p) Inputs field where
  main := main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c3
  rw [←c2, ←c3] at c1
  exact eq_div_of_mul_eq h_assumptions c1

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [add_neg_eq_zero]; field_simp [h_assumptions]
  · ring
  · ring

def circuit : FormalCircuit (F p) Inputs field :=
  {
    elaborated with
    Assumptions,
    Spec,
    soundness,
    completeness
  }

end Ragu.Circuits.Element.DivNonzero
