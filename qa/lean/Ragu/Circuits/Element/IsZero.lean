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
  let ⟨x1, iz, zp⟩ ← Core.AllocMul.circuit fun env =>
    let xv := Expression.eval env input
    ⟨xv, (if xv = 0 then (1 : F p) else 0), 0⟩
  assertZero (x1 - input)
  assertZero zp
  let ⟨x2, _, inz⟩ ← Core.AllocMul.circuit fun env =>
    let xv := Expression.eval env input
    ⟨xv, xv⁻¹, (if xv = 0 then (0 : F p) else 1)⟩
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
  circuit_proof_start [Core.AllocMul.circuit, Core.AllocMul.Spec]
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h_holds
  rw [add_neg_eq_zero] at c2 c5
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
  circuit_proof_start [Core.AllocMul.circuit, Core.AllocMul.ProverSpec]
  obtain ⟨⟨_, h0, h1, h2⟩, ⟨_, h3, h4, h5⟩⟩ := h_env
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0]; ring
  · rw [h2]
    split_ifs with hx
    · rw [hx]; ring
    · ring
  · rw [h3]; ring
  · rw [h5, h1]
    split_ifs with hx
    · rw [hx]; simp
    · rw [mul_inv_cancel₀ hx]; ring

def circuit : FormalCircuit (F p) field field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.IsZero
