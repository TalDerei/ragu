import Clean.Circuit
import Ragu.Core
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
  hint : UnconstrainedDep Core.AllocMul.Row F
deriving CircuitType

@[circuit_norm] lemma eval_verifier {F : Type} [Field F] (env : Environment F) (input : Var Input F) :
  eval env input = CircuitType.evalVerifier env input := CircuitType.eval_verifier env input

@[circuit_norm] lemma eval_prover {F : Type} [Field F] (env : ProverEnvironment F) (input : Var Input F) :
  eval env input = CircuitType.evalProver env input := CircuitType.eval_prover env input

-- quotient * denominator = numerator, with denominator = y, numerator = x
def main (input : Var Input (F p))
    : Circuit (F p) (Var field (F p)) := do
  let ⟨x, y, hint⟩ := input
  let ⟨quotient, denominator, numerator⟩ ← Core.AllocMul.circuit hint
  assertZero (x - numerator)
  assertZero (y - denominator)
  return quotient

def ProverAssumptions (input : ProverValue Input (F p))
    (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  input.hint.y = input.y ∧ input.hint.x * input.hint.y = input.x ∧
    (input.y ≠ 0 ∨ input.x = 0)

-- The disjunction `y ≠ 0 ∨ x ≠ 0` (rather than just `y ≠ 0`) reflects what the
-- circuit actually enforces via `quotient · y = x`:
--  * `y ≠ 0`: quotient is forced to `x / y`.
--  * `y = 0 ∧ x ≠ 0`: no valid witness exists; any prover transcript fails.
--  * `y = 0 ∧ x = 0`: quotient is unconstrained (premise is false, Spec is
--    vacuously true).
-- Callers of this gadget must establish `(x, y) ≠ (0, 0)` upstream or accept
-- the unconstrained-output carve-out. See `element.rs:273-280` for the
-- corresponding Rust `div_nonzero` doc comment.
def Spec (input : Value Input (F p))
    (out : field (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 ∨ input.x ≠ 0 → out = input.x / input.y

/-- Unconditional: the output wire equals the prover's hinted quotient. This is
exposed so that downstream circuits can reason about the witness value even in
the degenerate `(x, y) = (0, 0)` case where `GeneralSpec`'s premise fails. -/
def ProverSpec (input : ProverValue Input (F p))
    (out : field (F p)) (_hint : ProverHint (F p)) :=
  out = input.hint.x

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  localLength _ := 3

theorem soundness : GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Spec
  ]
  rw [← h_input] at *
  simp at h_holds ⊢
  grind

theorem completeness
    : GeneralFormalCircuit.WithHint.Completeness (F p) elaborated
        ProverAssumptions ProverSpec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Spec, Core.AllocMul.ProverSpec,
    ProverAssumptions, ProverSpec
  ]
  obtain ⟨_, h_x_eq, h_y_eq, h_z_eq⟩ := h_env
  rw [← h_input] at h_assumptions ⊢
  simp only at h_assumptions ⊢
  obtain ⟨h_y_in, h_z_in, _⟩ := h_assumptions
  constructor
  · rw [add_neg_eq_zero, add_neg_eq_zero]
    refine ⟨?_, ?_⟩
    · rw [h_z_eq]; exact h_z_in.symm
    · rw [h_y_eq]; exact h_y_in.symm
  · exact h_x_eq

def circuit : GeneralFormalCircuit.WithHint (F p) Input field :=
  { elaborated with
    Spec := Spec,
    ProverAssumptions := ProverAssumptions,
    ProverSpec := ProverSpec,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Element.DivNonzero
