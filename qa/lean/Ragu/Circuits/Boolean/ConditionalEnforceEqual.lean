import Clean.Circuit
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Boolean.ConditionalEnforceEqual
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  cond : F
  a : F
  b : F
deriving ProvableStruct

/-- `Boolean::conditional_enforce_equal` emits a custom 3-wire gate plus
three extra constraints:

- Gate: `cond_wire · diff_wire = zero_wire`.
- `cond_wire = cond` (input boolean).
- `diff_wire = a - b` (expressed as `diff_wire - a + b = 0`).
- `zero_wire = 0`.

Together these enforce `cond · (a - b) = 0`: when `cond = 0` the constraint
is trivially satisfied, and when `cond = 1` it forces `a = b`. -/
def main (input : Var Input (F p)) : Circuit (F p) (Var unit (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let cv := Expression.eval env input.cond
    let av := Expression.eval env input.a
    let bv := Expression.eval env input.b
    (⟨cv, av - bv, 0⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - input.cond)
  assertZero (y - input.a + input.b)
  assertZero z

/-- Completeness assumption: `cond ∈ {0, 1}` (for a well-formed gadget
invocation) and, when `cond = 1`, `a = b` (otherwise the honest prover
cannot satisfy the gate constraint). These preconditions are *not* used
by soundness — the constraints alone force `cond · (a - b) = 0`. -/
def Assumptions (input : Input (F p)) (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  (input.cond = 0 ∨ input.cond = 1) ∧ (input.cond = 1 → input.a = input.b)

/-- The verifier learns `cond · (a - b) = 0` unconditionally from the
constraints. Stated independently of `Assumptions` so the trusted
claim doesn't mislead callers into thinking they need to provide `a = b`
as a precondition — the constraints *enforce* that when `cond = 1`. -/
def Spec (input : Input (F p)) (_out : Unit) (_data : ProverData (F p)) :=
  input.cond * (input.a - input.b) = 0

instance elaborated : ElaboratedCircuit (F p) Input unit where
  main
  localLength _ := 3

theorem soundness : GeneralFormalCircuit.Soundness (F p) elaborated Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3, c4⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2
  -- c1 : (env.get i₀) * (env.get (i₀+1)) = env.get (i₀+1+1)
  -- c2 : env.get i₀ = input_cond
  -- c3 : (env.get (i₀+1)) + -input_a + input_b = 0
  -- c4 : env.get (i₀+1+1) = 0
  -- Goal : input_cond * (input_a - input_b) = 0
  linear_combination c1 - env.get (i₀ + 1) * c2 - input_cond * c3 + c4

theorem completeness : GeneralFormalCircuit.Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  obtain ⟨h_bool, h_eq⟩ := h_assumptions
  have h0 := h_env (0 : Fin 3)
  have h1 := h_env (1 : Fin 3)
  have h2 := h_env (2 : Fin 3)
  simp only [toElements, circuit_norm, explicit_provable_type, List.sum] at h0 h1 h2
  norm_num at h0 h1 h2
  simp at h0 h1 h2
  rw [show i₀ + 1 + 1 = i₀ + 2 from by omega]
  rw [h0, h1, h2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- gate: cond * (a - b) = 0, holds under the cond-bool + a=b-when-cond=1 assumption
    rcases h_bool with hc0 | hc1
    · rw [hc0]; ring
    · rw [hc1, h_eq hc1]; ring
  · ring
  · ring
  · ring

def circuit : GeneralFormalCircuit (F p) Input unit :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Boolean.ConditionalEnforceEqual
