# Example: a tiny multiplication circuit

For a minimal example that shows the Circuit monad, let's define a simple multiplication circuit.

```lean
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  x: F
  y: F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var field (F p)) := do
  let ⟨x, y⟩ := input

  -- allocate a new variable, witnessing the result
  let z ← witness fun eval => eval x * eval y

  -- add the constraint z = x * y
  assertZero (x * y - z)

  return z
```

Let's now do a step-by-step walk-through of this code.

### Prime assumptions

The circuit is parameterized by a natural number `p`, which is the characteristic of the base field.
This particular example works over a prime field, however Clean circuits can be written also for non-prime fields.

Introducing a `variable` means that all subsequent definition will have it as an implicit parameter. This is a convenient way of parametrizing every definition in a Lean section by the same variable.

- `{p : ℕ}` introduces a natural number variable `p`.
- `[Fact p.Prime]` is a typeclass assumption telling Lean that we assume that `p` is prime. Every concrete instantiation of circuits will have to provide a proof that the concrete `p` is prime to make instantiation possible.

Clean defines a type constructor `F` to define prime fields: `F p` is the field of elements modulo `p`.

### Input structure

This declares the input type of the circuit.

```lean
structure Inputs (F : Type) where
  x: F
  y: F
deriving ProvableStruct
```

A few details matter here:

- `Inputs` is a structure with two fields, `x` and `y`.
- The parameter `(F : Type)` means that the same structure can be instantiated with different types.

> [!TIP]
> Provable types can also be thought of as a "structured generic container of objects of type `F`". We will discuss provable types in a later section, but the main intuition is that they provide "shape templates" that can be filled with different `F`s depending on the context.

The line

```lean
deriving ProvableStruct
```

tells Clean to automatically build the `ProvableType` machinery for this structure.
Informally, this means Clean learns how to:

- view `Inputs` as a structured collection of field elements,
- allocate variables for it during witness operations,
- convert it to and from vectors of field elements, and
- use it as a typed circuit input or output.

Without `ProvableStruct`, Clean would not know how to represent `Inputs` inside a circuit.

Two very important instantiations that are useful for circuits are:
- `Inputs (F p)`: this is a collection of two concrete field elements in `F p`.
- `Inputs (Expression (F p))`: this is a collection of two expressions, which can be used in circuits to define constraints. Expressions are polynomials whose variables are witness locations. Expressions are the main objects manipulated by the Clean framework, and this type is so important that there is a very common alias for it: `Var Inputs (F p)`.

### Circuit type

The circuit body definition is:

```lean
def main (input : Var Inputs (F p)) : Circuit (F p) (Var field (F p)) := do
```

This line is dense, so it is worth unpacking carefully.

- `main` is the circuit-building function name.
- `input : Var Inputs (F p)` is an input parameter to the `main` function. It means the input is not given as concrete field values, but as expressions arranged in the shape of `Inputs`.
- `: Circuit (F p) (Var field (F p))` means that `main` returns a `Circuit`-wrapped result, which is `(Var field (F p))`.

Since `field` is the one-element provable type for a single field element, `Var field (F p)` is just the symbolic representation of one output variable.
In other words, this circuit returns one field element as output.

### Monadic block

The trailing `:= do` means the `main` body is written using Lean's monadic `do` notation.
In this setting, every line in the block contributes to a value of type

```lean
Circuit (F p) (Var field (F p))
```

So each step may:

- allocate new witness variables,
- append constraints to the operation list, and
- return a symbolic output for the rest of the circuit.

### Input destructuring

This destructures the structured input:

```lean
let ⟨x, y⟩ := input
```

Because `input` has type `Var Inputs (F p)`, the names `x` and `y` now refer to the two input expressions stored in that structure.

### Witness allocation

The circuit allocates one variable for the output `z` using a `witness` call.

```lean
let z ← witness fun eval => eval x * eval y
```

- `witness` is a circuit operation that allocates a fresh local variable.
- `let z ←` binds the newly allocated symbolic variable to the name `z` for the rest of the `do` block.
- `fun eval => eval x * eval y` is a closure that takes in input the current environment, and produces a concrete assignment to the new variable. Here, `eval` is just a function mapping expressions to concrete values.

After this line `z` is a new symbolic variable inside the circuit, and the honest prover will populate that variable as the product of the concrete values of `x` and `y`.

### Constraints

Right now, `z` is completely unconstrained, so we need to emit a constraint so that the circuit becomes useful:

```lean
assertZero (x * y - z)
```

The expression `x * y - z` is a symbolic arithmetic expression. Calling `assertZero` on it means the circuit adds the constraint

```lean
x * y - z = 0
```

### Output value

The final line is:

```lean
return z
```

This says that the output of the circuit is the symbolic variable `z`.
It does not allocate anything new and it does not add constraints, it only selects what the circuit returns as its result.
Because `z` has type `Var field (F p)`, the whole `do` block returns exactly the output type promised in the type of `main`.
