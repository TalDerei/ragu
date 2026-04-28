import Clean.Circuit
import Clean.Gadgets.Boolean
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Boolean.ConditionalSelect
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  cond : F
  a : F
  b : F
deriving ProvableStruct

/-- `Boolean::conditional_select(a, b)` emits one mul gate producing
`cond * (b - a)`, with the two factor wires constrained via
`enforce_equal` to `cond` and `b - a` respectively. The returned
element is the virtual expression `a + cond * (b - a)`. -/
def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env =>
    let cv := Expression.eval env input.cond
    let av := Expression.eval env input.a
    let bv := Expression.eval env input.b
    (⟨cv, bv - av, cv * (bv - av)⟩ : Core.AllocMul.Row (F p))
    : Circuit (F p) (Var Core.AllocMul.Row (F p)))
  assertZero (x * y - z)
  assertZero (x - input.cond)
  assertZero (y - (input.b - input.a))
  return input.a + z

/-- Caller must promise `cond` is boolean — without it, the "select"
description below doesn't hold (the underlying circuit computes
`a + cond · (b - a)`, which only collapses to a select when `cond ∈ {0, 1}`). -/
def Assumptions (input : Input (F p)) :=
  IsBool input.cond

/-- High-level operation: select `b` when `cond = 1`, else `a`. -/
def Spec (input : Input (F p)) (out : F p) :=
  out = if input.cond = 1 then input.b else input.a

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨c1, c2, c3⟩ := h_holds
  rw [add_neg_eq_zero] at c1 c2 c3
  -- The output is `input_a + env_z`. From the wire constraints,
  -- env_z = env_x * env_y = input_cond * (input_b - input_a).
  rcases h_assumptions with hc0 | hc1
  · rw [hc0, if_neg (by norm_num : (0 : F p) ≠ 1), ← c1, c2, c3, hc0]
    ring
  · rw [hc1, if_pos rfl, ← c1, c2, c3, hc1]
    ring

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
  refine ⟨?_, ?_, ?_⟩ <;> ring

def circuit : FormalCircuit (F p) Input field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Boolean.ConditionalSelect
