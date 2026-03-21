# A full example

Let's walk through a simple example that shows all the concepts discussed so far.
This is part of the Ragu gadgets currently formalized.
Let's say we want to define a division circuit, that guarantees the correctness of the output as long as the provided denominator is non-zero.

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

def main (input : Var Inputs (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨quotient, denominator, numerator⟩ ← subcircuit Core.AllocMul.circuit ()

  assertZero (input.x - numerator)
  assertZero (input.y - denominator)

  return quotient

def Assumptions (input : Inputs (F p)) := sorry

def Spec (input : Inputs (F p)) (out : field (F p)) := sorry

instance elaborated : ElaboratedCircuit (F p) Inputs field where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) Inputs field :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Element.DivNonzero
```

In this template we define the input shape, which is a structure with two inputs: `x` and `y`.
The goal of the template is to return the division over the field `x / y`, as long as `y` is different than zero.
The circuit invokes as a subcircuit `Core.AllocMul.circuit`, which allocates a triple `(a, b, c)` and enforces that `a * b = c`, returning the allocated triple to the caller.
The division circuit enforces that the input `x` is equal to the third component of the triple, and that the input `y` is equal to the second component of the triple, returning the first component.

Intuitively, to compute `x / y`, the prover witnesses the result `z`, and then checks that `z * y = x`.
Notice that if the caller provides `y = 0`, the circuit makes no guarantees.
To specify this behaviour, we can fill in the `Assumptions`, specifying that the caller must provide a non-zero `y` value.

```lean
def Assumptions (input : Inputs (F p)) :=
  input.y ≠ 0
```

The property that is provided by the circuit is that the output is the result of the division of `x` and `y`.

```lean
def Spec (input : Inputs (F p)) (out : field (F p)) :=
  out = input.x / input.y
```

## Soundness proof

Let's start working on the soundness proof.

```lean
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  sorry
```

Lean will show a not particularly useful goal that we have to prove:

```lean
p : ℕ
inst✝ : Fact (Nat.Prime p)
⊢ Soundness (F p) elaborated Assumptions Spec
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
i₀ : ℕ
env : Environment (F p)
input_x input_y : F p
h_assumptions : input_y ≠ 0
input_var_x input_var_y : Expression (F p)
h_input : Expression.eval env input_var_x = input_x ∧ Expression.eval env input_var_y = input_y
h_holds : (Core.AllocMul.circuit.Assumptions (eval env ()) →
    Core.AllocMul.circuit.Spec (eval env ())
      { x := Expression.eval env (ElaboratedCircuit.output () i₀).x,
        y := Expression.eval env (ElaboratedCircuit.output () i₀).y,
        z := Expression.eval env (ElaboratedCircuit.output () i₀).z }) ∧
  input_x + -Expression.eval env (ElaboratedCircuit.output () i₀).z = 0 ∧
    input_y + -Expression.eval env (ElaboratedCircuit.output () i₀).y = 0
⊢ Expression.eval env (ElaboratedCircuit.output () i₀).x = input_x / input_y
```

Let's describe every important hypothesis and the goal:
- `input_x` and `input_y` are the input field elements.
- `h_assumptions` is the hypothesis that `Assumptions` hold on the input. In this case it is `input_y ≠ 0`.
- `h_holds` is the hypothesis that the constraints hold. Remember, we are trying to prove soundness: we need to prove that for every input, under the hypotheses that they satisfy the assumptions and constraints hold, the specification holds as well. 
- The goal is the specification.

First let's rename the elaborated output that is arising from the subcircuit call, and unpack the constraint hypothesis.

```lean
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  set quotient := Expression.eval env (ElaboratedCircuit.output (self:=Core.AllocMul.elaborated) (F:=F p) () i₀).x
  set denominator := Expression.eval env (ElaboratedCircuit.output (self:=Core.AllocMul.elaborated) (F:=F p) () i₀).y
  set numerator := Expression.eval env (ElaboratedCircuit.output (self:=Core.AllocMul.elaborated) (F:=F p) () i₀).z
  obtain ⟨c1, c2, c3⟩ := h_holds
```

Now the hypotheses are cleaner:

```lean
h_assumptions : input_y ≠ 0
c1 : Core.AllocMul.circuit.Assumptions (eval env ()) →
  Core.AllocMul.circuit.Spec (eval env ()) { x := quotient, y := denominator, z := numerator }
c2 : input_x + -numerator = 0
c3 : input_y + -denominator = 0
⊢ quotient = input_x / input_y
```

Let's discuss each circuit hypothesis:
- `c1` is a constraint hypothesis derived by a subcircuit call. We will discuss compositionality later, but it is an implication: the `Spec` of the subcircuit is true, conditioned on the fact that the caller is able to discharge the `Assumptions` hypothesis. In this case, `Core.AllocMul.circuit` has no assumptions, so this can be discharged automatically.
- `c2` and `c3` are direct translations of constraints derived by the two `assertZero` calls.

Let's simplify definitions and statements at constraints and at the goal:

```lean
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  set quotient := Expression.eval env (ElaboratedCircuit.output (self:=Core.AllocMul.elaborated) (F:=F p) () i₀).x
  set denominator := Expression.eval env (ElaboratedCircuit.output (self:=Core.AllocMul.elaborated) (F:=F p) () i₀).y
  set numerator := Expression.eval env (ElaboratedCircuit.output (self:=Core.AllocMul.elaborated) (F:=F p) () i₀).z
  obtain ⟨c1, c2, c3⟩ := h_holds
  simp [circuit_norm, Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec] at c1 c2 c3 ⊢
```

Now the proof state is simpler:

```lean
h_assumptions : input_y ≠ 0
c2 : input_x + -numerator = 0
c3 : input_y + -denominator = 0
c1 : quotient * denominator = numerator
⊢ quotient = input_x / input_y
```

At this point, it is just a matter of some standard algebraic manipulation, as all Clean-specific objects have been simplified away. The goal is closed by the following proof:

```lean
theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  set quotient := Expression.eval env (ElaboratedCircuit.output (self:=Core.AllocMul.elaborated) (F:=F p) () i₀).x
  set denominator := Expression.eval env (ElaboratedCircuit.output (self:=Core.AllocMul.elaborated) (F:=F p) () i₀).y
  set numerator := Expression.eval env (ElaboratedCircuit.output (self:=Core.AllocMul.elaborated) (F:=F p) () i₀).z
  obtain ⟨c1, c2, c3⟩ := h_holds
  simp [circuit_norm, Core.AllocMul.circuit, Core.AllocMul.Assumptions, Core.AllocMul.Spec] at c1 c2 c3 ⊢
  rw [add_neg_eq_zero] at c2 c3
  rw [←c2, ←c3] at c1
  apply eq_div_of_mul_eq <;> assumption
```

## Completeness proof

TODO
