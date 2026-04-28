# Operations

The result of running a `Circuit` is a list of operations. Operations are the most low-level description of a circuit, and every property about circuits ultimately talks about operations.

Clean uses two closely related representations: `FlatOperation` and `Operation`.

## Flat operations

The flat representation is:

```lean
inductive FlatOperation (F : Type) where
  | witness : (m : ℕ) → (ProverEnvironment F → Vector F m) → FlatOperation F
  | assert : Expression F → FlatOperation F
  | lookup : Lookup F → FlatOperation F
```

So a flat operation can:

- introduce `m` witness variables at the current offset, implicitly incrementing the current offset by `m`,
- assert that an expression is zero,
- perform a lookup.

We have not talked about lookup support in Clean, mainly because it is not needed for Ragu. It suffices to say that a lookup enforces a set membership relation for some variables into some other table.

> [!NOTE]
> A circuit in Clean, in its most bare-bones form, is just a list of operations, i.e., a sequence of allocations and constraints.
> Every abstraction built on top just provides a better API and better ergonomics to define this list.


Working with flat operations can become unmanageable when working with large circuits. Also we would like to exploit the regularity of this list, if possible.
That's where *subcircuits* come into play: they represent units of circuits that can be instantiated at any offset, and provide some well-defined interface to interact with the whole circuit.

For the non-flat operation, we add one `subcircuit` constructor:

```lean
inductive Operation (F : Type) [Field F] where
  | witness : (m : ℕ) → (compute : ProverEnvironment F → Vector F m) → Operation F
  | assert : Expression F → Operation F
  | lookup : Lookup F → Operation F
  | subcircuit : {n : ℕ} → Subcircuit F n → Operation F
```

So `Operation` can be viewed as a nested representation of circuits, composed of allocations, constraint definitions and subcircuit invocations.

## Subcircuits

A subcircuit call stores more than just a list of low-level operations:

```lean
structure Subcircuit (F : Type) [Field F] (offset : ℕ) where
  ops : NestedOperations F
  Soundness : Environment F → Prop
  Completeness : ProverEnvironment F → Prop
  UsesLocalWitnesses : ProverEnvironment F → Prop
  localLength : ℕ
  ...
```

The important point here is that a subcircuit carries: its own operations, its witness length (i.e., how many variables are allocated internally) and the logical statements needed for compositional proofs.
Clean can reason about a subcircuit as one atomic operation at the outer level, while still knowing how to expand it to primitive operations when needed.

Notice the asymmetry between `Soundness` and the other two: soundness cannot see the prover's `hint`, while completeness and witness-generation can.

## Flattening

To move from operations to flat operations, Clean defines an important function:

```lean
def Operations.toFlat : Operations F → List (FlatOperation F)
  | [] => []
  | .witness m c :: ops => .witness m c :: toFlat ops
  | .assert e :: ops => .assert e :: toFlat ops
  | .lookup l :: ops => .lookup l :: toFlat ops
  | .subcircuit s :: ops => s.ops.toFlat ++ toFlat ops
```

Flattening preserves ordinary witness/assert/lookup operations, and recursively replaces a `subcircuit` call by the flat operations inside that subcircuit.
Once operations are flattened, the subcircuit structure is lost.
