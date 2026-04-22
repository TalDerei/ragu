import Clean.Circuit
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.IsZero
variable {p : ℕ} [Fact p.Prime]

/-- `is_zero(x)` implements the standard inverse trick over two gates:

- Gate 1 enforces `x · is_zero = 0`, so when `x ≠ 0` we must have `is_zero = 0`.
- Gate 2 enforces `x · inv = 1 - is_zero`, which is satisfiable (by picking
  `inv = x⁻¹`) when `x ≠ 0` and forces `is_zero = 1` when `x = 0`.

Together these pin down `is_zero = if x = 0 then 1 else 0`. -/
def main (input : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨x1, iz, zp⟩ ← (witness fun env =>
    let xv := Expression.eval env input
    (⟨xv, (if xv = 0 then (1 : F p) else 0), 0⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x1 * iz - zp)
  assertZero (x1 - input)
  assertZero zp
  let ⟨x2, inv, inz⟩ ← (witness fun env =>
    let xv := Expression.eval env input
    (⟨xv, xv⁻¹, (if xv = 0 then (0 : F p) else 1)⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x2 * inv - inz)
  assertZero (x2 - input)
  assertZero (inz - 1 + iz)
  return iz

def Assumptions (_input : F p) := True

/-- The output equals `1` when the input is zero and `0` otherwise. -/
def Spec (input : F p) (out : F p) :=
  out = if input = 0 then 1 else 0

instance elaborated : ElaboratedCircuit (F p) field field where
  main
  localLength _ := 6

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c4 c5
  -- c1 : x1 * iz = zp        c4 : x2 * inv = inz
  -- c2 : x1 = input           c5 : x2 = input
  -- c3 : zp = 0               c6 : inz - 1 + iz = 0
  by_cases hx : input = 0
  · -- Case input = 0: derive iz = 1 from gate 2's chain.
    simp only [hx, if_true]
    rw [c5, hx, zero_mul] at c4   -- c4 : 0 = env.get (i₀+5)   (inz = 0)
    linear_combination c4 + c6
  · -- Case input ≠ 0: derive iz = 0 from gate 1 + cancellation.
    simp only [hx, if_false]
    rw [c2, c3] at c1   -- c1 : input * env.get (i₀+1) = 0
    rcases mul_eq_zero.mp c1 with hinp | hiz
    · exact absurd hinp hx
    · exact hiz

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  obtain ⟨h_env1, h_env2⟩ := h_env
  have h0 := h_env1 (0 : Fin 3)
  have h1 := h_env1 (1 : Fin 3)
  have h2 := h_env1 (2 : Fin 3)
  have h3 := h_env2 (0 : Fin 3)
  have h4 := h_env2 (1 : Fin 3)
  have h5 := h_env2 (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum]
    at h0 h1 h2 h3 h4 h5
  norm_num at h0 h1 h2 h3 h4 h5
  simp at h0 h1 h2 h3 h4 h5
  -- Normalize `[1,1,1].sum` to `3` in the goal.
  simp only [show ([1, 1, 1] : List ℕ).sum = 3 from rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- gate 1 : x1 * iz - zp = 0
    rw [h0, h1, h2]
    split_ifs with hx
    · rw [hx]; ring
    · ring
  · -- x1 - input = 0
    rw [h0]; ring
  · -- zp = 0
    rw [h2]
  · -- gate 2 : x2 * inv - inz = 0
    rw [show i₀ + 3 + 1 + 1 = i₀ + 3 + 2 from by omega, h3, h4, h5]
    split_ifs with hx
    · rw [hx]; simp
    · rw [mul_inv_cancel₀ hx]; ring
  · -- x2 - input = 0
    rw [h3]; ring
  · -- inz - 1 + iz = 0
    rw [show i₀ + 3 + 1 + 1 = i₀ + 3 + 2 from by omega, h5, h1]
    split_ifs with hx <;> ring

def circuit : FormalCircuit (F p) field field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.IsZero
