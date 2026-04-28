# Provable types and structs

Clean needs a way to talk about structured collections of elements, in two main contexts:

- as ordinary mathematical values, such as field elements, vectors, or records, and
- as symbolic circuit variables and expressions.

The abstraction that supports this is the notion of a **provable type**.

## Type maps

At the base of the design is the definition

```lean
@[reducible]
def TypeMap := Type → Type
```

A `TypeMap` is a type constructor that takes a type, which can be thought of the type of elements, and returns a structured type built out of them.

Two important built-in examples are defined in Lean as:

```lean
@[reducible]
def field : TypeMap := id

@[reducible]
def fields (n : ℕ) := fun F => Vector F n
```

- `field := id` means that `field F` is just `F`, so this type map represents exactly one field element.
- `fields n := fun F => Vector F n` means that `fields n F` is a vector of `n` elements of type `F`.

As we have already seen, a user-defined structure like

```lean
structure Inputs (F : Type) where
  x : F
  y : F
```

is also a type map.

> [!NOTE]
> `@[reducible]` is a technical tag that tells Lean to always unfold this definition when, for example, checking if two objects are *definitionally* equal.
> For a more in-depth explanation, see [this thread](https://proofassistants.stackexchange.com/questions/2457/what-is-the-precise-meaning-of-reducible).


Given a type map `M`, Clean defines the type of "symbolic circuit variables" associated to `M` as

```lean
@[reducible]
def Var (M : TypeMap) (F : Type) := M (Expression F)
```

This is one of the most important aliases in the framework.
If `M F` means "concrete values of shape `M`", then `Var M F` means "symbolic expressions of the same shape `M`".


## Provable types

A `TypeMap` alone does not provide enough guarantees about its structure, what we want to represent is a structured generic container. The central class representing this is `ProvableType`:

```lean
class ProvableType (M : TypeMap) where
  size : ℕ
  toElements {F : Type} : M F -> Vector F size
  fromElements {F : Type} : Vector F size -> M F
```


A `ProvableType` is a type map that can be flattened to a fixed-length vector of field elements and reconstructed from that vector.
This is exactly the structure Clean needs in order to:

- allocate variables for a value of type `M`,
- serialize a value into witness slots,
- evaluate symbolic variables in an environment, and
- pass typed objects through circuit boundaries while still knowing their low-level field layout.

## Built-in provable types

Some basic instances of `ProvableType` provided by Clean are:

```lean
@[reducible] def field : TypeMap := id

instance : ProvableType field where
  size := 1
  toElements x := #v[x]
  fromElements := fun ⟨⟨[x]⟩, _⟩ => x
```

So a single field element is a provable type of size `1`.

Vectors of field elements are also trivially provable:

```lean
@[reducible]
def fields (n : ℕ) := fun F => Vector F n

instance : ProvableType (fields n) where
  size := n
  toElements x := x
  fromElements v := v
```

Clean also provides a `ProvableVector` constructor. Intuitively, a vector of provable types is provable.

```lean
@[reducible]
def ProvableVector (α : TypeMap) (n : ℕ) := fun F => Vector (α F) n
```

## Evaluation and variable allocation

Once a type implements the `ProvableType` class, Clean can define generic operations on it.
Two important ones are:

```lean
def eval (env : ProverEnvironment F) (x : Var α F) : α F := ...

def varFromOffset (α : TypeMap) [ProvableType α] (offset : ℕ) : Var α F := ...
```

- `eval` turns a symbolic object into a concrete one by evaluating each of its underlying expressions in an environment. It returns the evaluations packaged in the same provable type shape.
- `varFromOffset` returns the provable type structure, filled with fresh variables starting from `offset` in the environment. This is used internally in the allocation functions, and is useful in proofs to retrieve structure from unstructured portions of the environment.


## Provable structs

Many circuit inputs and outputs are naturally expressed as Lean structures rather than tuples or raw vectors. Clean supports this with the `ProvableStruct` class:

```lean
class ProvableStruct (α : TypeMap) where
  components : List WithProvableType
  toComponents {F : Type} : α F → ProvableTypeList F components
  fromComponents {F : Type} : ProvableTypeList F components → α F
```

The idea is that a structure is broken into a list of components, each component is itself a provable type, and the structure can be converted to and from that component list.
Once this is available, Clean automatically derives a `ProvableType` instance from it:

```lean
instance ProvableType.fromStruct {α : TypeMap} [ProvableStruct α] : ProvableType α where
  size := combinedSize α
  toElements x := ...
  fromElements v := ...
```

Using `ProvableStruct` and `ProvableVector`, most high-level structured field-element collections can be represented, by composing primitive provable types together.

Typically, users will never write any `ProvableStruct` instances by hand. Instead they can derive it automatically:

```lean
structure Inputs (F : Type) where
  x : F
  y : F
deriving ProvableStruct
```

The deriving handler generates the corresponding `ProvableStruct` instance automatically, provided the fields are themselves supported shapes.
The supported field patterns in the structure include:

- `F`
- `M F`, where `M` already has a `ProvableType` instance
- `Vector F n`
- `Vector (M F) n`, where `M` already has a `ProvableType` instance
