# A full example

Let's walk through a simple example that shows all the concepts discussed so far.
This is part of the Ragu gadgets currently formalized.
Let's say we want to define a division circuit, that guarantees the correctness of the output as long as the provided denominator or numerator is non-zero.

Let's start with a basic template definition.

```lean
import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.DivNonzero
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct

-- quotient * denominator = numerator, with denominator = y, numerator = x
def main (idx : ℕ) (input : Var Inputs (F p))
    : Circuit (F p) (Var field (F p)) := do
  let ⟨quotient, denominator, numerator⟩ ← Core.AllocMul.circuit idx ()
  assertZero (input.x - numerator)
  assertZero (input.y - denominator)
  return quotient

def GeneralAssumptions (idx : ℕ)
    (input : Inputs (F p)) (_data : ProverData (F p)) (hint : ProverHint (F p)) :=
  let r := Core.AllocMul.readRow hint idx
  r.y = input.y ∧ r.x * r.y = input.x ∧ (input.y ≠ 0 ∨ input.x = 0)

def GeneralSpec (input : Inputs (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 ∨ input.x ≠ 0 → out = input.x / input.y

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) Inputs field where
  main := main idx
  localLength _ := 3

theorem generalSoundness (idx : ℕ)
    : GeneralFormalCircuit.Soundness (F p) (elaborated idx) GeneralSpec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec, GeneralSpec
  ]
  grind

theorem generalCompleteness (idx : ℕ)
    : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (GeneralAssumptions idx) := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.Spec, Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨_, h_x_eq, h_y_eq, h_z_eq⟩ := h_env
  simp only [GeneralAssumptions] at h_assumptions
  obtain ⟨h_y_in, h_z_in, _⟩ := h_assumptions
  rw [add_neg_eq_zero, add_neg_eq_zero]
  refine ⟨?_, ?_⟩
  · rw [h_z_eq]; exact h_z_in.symm
  · rw [h_y_eq]; exact h_y_in.symm

def generalCircuit (idx : ℕ)
    : GeneralFormalCircuit (F p) Inputs field :=
  { elaborated idx with
    Assumptions := GeneralAssumptions idx,
    Spec := GeneralSpec,
    soundness := generalSoundness idx,
    completeness := generalCompleteness idx }

end Ragu.Circuits.Element.DivNonzero
```

In this template we define the input shape, which is a structure with two inputs: `x` and `y`.
The goal of the template is to return the division over the field `x / y`, as long as `x` or `y` is different from zero.
The circuit invokes as a subcircuit `Core.AllocMul.circuit`, which allocates a triple `(a, b, c)` and enforces that `a * b = c`, returning the allocated triple to the caller.
The division circuit enforces that the input `x` is equal to the third component of the triple, and that the input `y` is equal to the second component of the triple, returning the first component.

The `idx : ℕ` parameter picks one row of the prover's hint table that `AllocMul` reads during witness generation — the honest prover is expected to have precomputed a `(quotient, denominator, numerator)` triple at that position.

Intuitively, to compute `x / y`, the prover witnesses the result `z`, and then checks that `z * y = x`.
Notice that if the caller provides both `x = 0` and `y = 0`, the circuit makes no guarantees.

The property that is provided by the circuit is that, assuming either `x` or `y` is non-zero, the output is the result of the division of `x` and `y`.

```lean
def GeneralSpec (input : Inputs (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 ∨ input.x ≠ 0 → out = input.x / input.y
```

## Soundness proof

Let's start working on the soundness proof.

```lean
theorem generalSoundness (idx : ℕ)
    : GeneralFormalCircuit.Soundness (F p) (elaborated idx) GeneralSpec := by
  sorry
```

Lean will show a not particularly useful goal that we have to prove:

```lean
p : ℕ
inst✝ : Fact (Nat.Prime p)
idx : ℕ
⊢ GeneralFormalCircuit.Soundness (F p) (elaborated idx) GeneralSpec
```

The first thing to do is invoking the `circuit_proof_start` tactic, that will set up the proof, and get rid of most of the machinery going on behind the scenes.

```lean
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
```

The proof state now becomes more interesting:

```lean
p : ℕ
inst✝ : Fact (Nat.Prime p)
idx : ℕ
i₀ : ℕ
env : VerifierEnvironment (F p)
input_x input_y : F p
input_var_x input_var_y : Expression (F p)
h_input : Expression.eval env input_var_x = input_x ∧ Expression.eval env input_var_y = input_y
h_holds : (Core.AllocMul.circuit idx).Spec (eval env ())
    { x := Expression.eval env (ElaboratedCircuit.output () i₀).x,
      y := Expression.eval env (ElaboratedCircuit.output () i₀).y,
      z := Expression.eval env (ElaboratedCircuit.output () i₀).z }
    env.data ∧
  input_x + -Expression.eval env (ElaboratedCircuit.output () i₀).z = 0 ∧
    input_y + -Expression.eval env (ElaboratedCircuit.output () i₀).y = 0
⊢ GeneralSpec { x := input_x, y := input_y } (Expression.eval env (ElaboratedCircuit.output () i₀).x) env.data
```

Let's describe every important hypothesis and the goal:
- `input_x` and `input_y` are the input field elements.
- `h_holds` is the hypothesis that the constraints hold. Remember, we are trying to prove soundness: we need to prove that for every input, under the hypotheses that they satisfy the assumptions and constraints hold, the specification holds as well. 
- The goal is the specification (which contains the assumption x or y is nonzero)

Here, some mathematical contents are still hidden behind the symbols. `circuit_proof_start` can replace symbols with their definitions. Instead of just `circuit_proof_start`, the same tactic with arguments will show more interesting things.

```lean
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec, GeneralSpec
  ]
```

Now the proof goal is more explicit:

```lean
p : ℕ
inst✝ : Fact (Nat.Prime p)
idx : ℕ
i₀ : ℕ
env : VerifierEnvironment (F p)
input_x input_y : F p
input_var_x input_var_y : Expression (F p)
h_input : Expression.eval env input_var_x = input_x ∧ Expression.eval env input_var_y = input_y
h_holds : Expression.eval env (Core.AllocMul.main idx () i₀).1.x * Expression.eval env (Core.AllocMul.main idx () i₀).1.y =
    Expression.eval env (Core.AllocMul.main idx () i₀).1.z ∧
  input_x + -Expression.eval env (Core.AllocMul.main idx () i₀).1.z = 0 ∧
    input_y + -Expression.eval env (Core.AllocMul.main idx () i₀).1.y = 0
⊢ input_y ≠ 0 ∨ input_x ≠ 0 → Expression.eval env (Core.AllocMul.main idx () i₀).1.x = input_x / input_y
```

We can see a big term `Expression.eval env (Core.AllocMul.main idx () i₀)` appears repeatedly, but all the ingredients are there. `h_input` is the assumption about the input. `h_holds` is what a verifier knows from constraints and the subcircuits.

A single `grind` tactic finishes the proof.

```lean
theorem generalSoundness (idx : ℕ)
    : GeneralFormalCircuit.Soundness (F p) (elaborated idx) GeneralSpec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec, GeneralSpec
  ]
  grind
```

## Completeness proof

TODO
