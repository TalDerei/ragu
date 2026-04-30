import Clean.Circuit
import Clean.Gadgets.Boolean
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Core.Mul

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
  let ⟨x, y, z⟩ ← Core.mul fun env =>
    ⟨env input.cond, env input.a - env input.b, 0⟩
  assertZero (x - input.cond)
  assertZero (y - input.a + input.b)
  assertZero z

def Assumptions (_input : Input (F p)) := True

/-- High-level operation: when `cond` is nonzero, the circuit forces `a = b`;
when `cond = 0`, the circuit imposes no relation between `a` and `b`. -/
def Spec (input : Input (F p)) :=
  input.cond ≠ 0 → input.a = input.b

instance elaborated : ElaboratedCircuit (F p) Input unit where
  main
  localLength _ := 3

theorem soundness : FormalAssertion.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  grind

theorem completeness : FormalAssertion.Completeness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [IsBool]
  and_intros
  · grind
  · grind
  · simp [← h_env.1]
    grind

def circuit : FormalAssertion (F p) Input :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Boolean.ConditionalEnforceEqual
