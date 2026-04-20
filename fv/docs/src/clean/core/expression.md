# Expressions and environment

Circuits in Clean are written symbolically. The basic objects are `Variable`, `Expression`, and `Environment`.

## Variables

At the lowest level, a variable is just an index, pointing to a particular position in the environment.

```lean
structure Variable (F : Type) where
  index : ℕ
```

Expressions are then defined as follows:

```lean
inductive Expression (F : Type) where
  | var : Variable F -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F
```

Expressions can be built from:
- variables, which are references to environment values,
- constant field elements,
- addition of two expressions,
- multiplication of two expressions.

Clean equips `Expression F` with the usual arithmetic notation, so circuit code can write expressions such as:

```lean
x * y - z
```

instead of manually using constructors like `Expression.mul` and `Expression.add`.

## Environments

Clean uses two environment structures, depending on who is allowed to look inside:

```lean
structure VerifierEnvironment (F : Type) where
  get : ℕ → F
  data : ProverData F

structure Environment (F : Type) extends VerifierEnvironment F where
  hint : ProverHint F
```

- `get` assigns a field element to each variable index.
- `data` stores auxiliary data that is committed into the proof — the verifier can access it (for example the content of a lookup table).
- `hint` is a runtime-only map the prover uses during witness generation. It is *not* committed and the verifier never observes it.

The split enforces that only the prover-facing side of the framework can see `hint`:

- **Soundness-path** objects (expression evaluation, `ConstraintsHold.Soundness`, a subcircuit's `Soundness`, the `Spec` of a formal circuit) take a `VerifierEnvironment`. They have no way to depend on a hint.
- **Completeness-path** objects (`ConstraintsHold.Completeness`, witness-generation callbacks, a subcircuit's `Completeness` and `UsesLocalWitnesses`) take the full `Environment`.

`Environment.toVerifierEnvironment` drops the hint and returns the verifier view. In Lean this is also registered as a coercion, so in many places the user can write `env : Environment F` where a `VerifierEnvironment F` is expected and Lean inserts the projection automatically; in the remaining cases the user writes `env.toVerifierEnvironment` explicitly.

## Evaluation

Expressions are evaluated in a verifier environment:

```lean
def eval (env : VerifierEnvironment F) : Expression F → F
  | var v => env.get v.index
  | const c => c
  | add x y => eval env x + eval env y
  | mul x y => eval env x * eval env y
```

Clean registers a `CoeFun` instance on both environment structs, so either kind of environment can be used directly as a function on expressions. That is why circuit code often writes:

```lean
env x
```

instead of:

```lean
Expression.eval env x
```

The `CoeFun` mechanism is a standard Lean feature that lets a value be applied as if it were a function.
