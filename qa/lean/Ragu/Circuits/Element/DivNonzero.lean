import Clean.Circuit
import Ragu.Core
import Ragu.Circuits.Core.Mul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

-- quotient * denominator = numerator, with denominator = y, numerator = x
def main (input : Var Input (F p)) : Circuit (F p) (Var field (F p)) := do
  let { x, y } := input
  let ⟨quotient, denominator, numerator⟩ ← Core.mul fun eval =>
    ⟨(eval x) / (eval y), (eval y), (eval x)⟩
  assertZero (x - numerator)
  assertZero (y - denominator)
  return quotient

def ProverAssumptions (input : Input (F p))
    (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  input.y ≠ 0

-- The disjunction `y ≠ 0 ∨ x ≠ 0` (rather than just `y ≠ 0`) reflects what the
-- circuit actually enforces via `quotient · y = x`:
--  * `y ≠ 0`: quotient is forced to `x / y`.
--  * `y = 0 ∧ x ≠ 0`: no valid witness exists; any prover transcript fails.
--  * `y = 0 ∧ x = 0`: quotient is unconstrained (premise is false, Spec is
--    vacuously true).
-- Callers of this gadget must establish `(x, y) ≠ (0, 0)` upstream or accept
-- the unconstrained-output carve-out. See `element.rs:273-280` for the
-- corresponding Rust `div_nonzero` doc comment.
def Assumptions (input : Input (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 ∨ input.x ≠ 0

def Spec (input : Input (F p))
    (out : field (F p)) (_data : ProverData (F p)) :=
  out = input.x / input.y

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  output _ offset := varFromOffset field offset
  localLength _ := 3

theorem soundness : GeneralFormalCircuit.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  grind

theorem completeness
    : GeneralFormalCircuit.Completeness (F p) elaborated ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_all

def circuit : GeneralFormalCircuit (F p) Input field :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    ProverAssumptions := ProverAssumptions,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Element.DivNonzero
