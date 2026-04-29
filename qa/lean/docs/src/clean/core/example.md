# A full example

Let's walk through a simple example that shows all the concepts discussed so far.
This is part of the Ragu gadgets currently formalized.
Let's say we want to define a division circuit, that guarantees the correctness of the output as long as the provided denominator or numerator is non-zero.

Let's start with a basic template definition.

```lean
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

def Assumptions (input : Input (F p)) (_data : ProverData (F p)) :=
  input.y ≠ 0 ∨ input.x ≠ 0

def ProverAssumptions (input : Input (F p))
    (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  input.y ≠ 0

def Spec (input : Input (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  out = input.x / input.y

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  output _ offset := varFromOffset field offset
  localLength _ := 3

theorem soundness : GeneralFormalCircuit.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  grind

theorem completeness :
    GeneralFormalCircuit.Completeness (F p) elaborated ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_all

def circuit : GeneralFormalCircuit (F p) Input field :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    ProverAssumptions := ProverAssumptions,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Element.DivNonzero
```

In this template we define the input shape, which is a structure with two inputs: `x` and `y`.
The goal of the template is to return the division over the field `x / y`, as long as `x` or `y` is different from zero.
The circuit invokes as a subcircuit `Core.mul`, which allocates a triple `(a, b, c)` and enforces that `a * b = c`, returning the allocated triple to the caller.
The division circuit enforces that the input `x` is equal to the third component of the triple, and that the input `y` is equal to the second component of the triple, returning the first component.

Intuitively, to compute `x / y`, the prover witnesses the result `z`, and then checks that `z * y = x`.
Notice that if the caller provides both `x = 0` and `y = 0`, the circuit makes no guarantees.

The property that is provided by the circuit is that, assuming either `x` or `y` is non-zero, the output is the result of the division of `x` and `y`.

```lean
def Spec (input : Input (F p)) (out : field (F p)) (_data : ProverData (F p)) :=
  out = input.x / input.y
```

## Soundness proof

Let's start working on the soundness proof.

```lean
theorem soundness : GeneralFormalCircuit.Soundness (F p) elaborated Assumptions Spec := by
  sorry
```

Lean will show a not particularly useful goal that we have to prove:

```lean
p : ℕ
inst✝ : Fact (Nat.Prime p)
⊢ GeneralFormalCircuit.Soundness (F p) elaborated Assumptions Spec
```

The first thing to do is invoking the `circuit_proof_start` tactic, that will set up the proof, and get rid of most of the machinery going on behind the scenes.
Internally, this tactic uses the `circuit_norm` simp set, so definitions such as `Core.mul`, its `Spec`, and its output shape are unfolded automatically.
For other circuits, pass additional definitions to `circuit_proof_start`, especially when using subcircuits to unfold their definitions, specs and assumptions.

```lean
theorem soundness : GeneralFormalCircuit.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
```

The proof state now becomes more interesting and already exposes the concrete constraints:

```lean
p : ℕ
inst✝ : Fact (Nat.Prime p)
i₀ : ℕ
env : Environment (F p)
input_x input_y : F p
input_var_x input_var_y : Expression (F p)
h_input : Expression.eval env input_var_x = input_x ∧ Expression.eval env input_var_y = input_y
h_assumptions : input_y ≠ 0 ∨ input_x ≠ 0
h_holds :
  env.get i₀ * env.get (i₀ + 1) = env.get (i₀ + 1 + 1) ∧
    input_x + -env.get (i₀ + 1 + 1) = 0 ∧ input_y + -env.get (i₀ + 1) = 0
⊢ env.get i₀ = input_x / input_y
```

Let's describe every important hypothesis and the goal:
- `input_x` and `input_y` are the input field elements.
- `h_assumptions` is the verifier-side precondition `input.y ≠ 0 ∨ input.x ≠ 0`.
- `h_holds` is the hypothesis that the constraints hold. It says the allocated row satisfies `quotient * denominator = numerator`, and that `numerator` and `denominator` were constrained to the input fields.
- The goal is the specification, under the verifier-side assumption that `x` or `y` is nonzero.

All the ingredients are there. The first conjunct of `h_holds` is the multiplication constraint, while the other two conjuncts connect the allocated row back to the input. From these facts, the field equation in the goal is immediate.

A single `grind` tactic finishes the proof.

```lean
theorem soundness : GeneralFormalCircuit.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  grind
```

## Completeness proof

TODO
