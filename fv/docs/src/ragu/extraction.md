# Extraction of Ragu circuits

This section describes how Ragu circuits are exported into `Clean` operations.
Intuitively, the extractor runs the circuit we want to formalize using the exporter driver, which logs every operation that the circuit emits.
The result is a symbolic trace of witness allocations and assertions, printed as Lean definitions in the same low-level language used by `Clean`.

By directly recording driver calls, and not directly interacting with any higher-level structure of the Rust code, the exporter is able to maintain a minimal trust surface.
Every exported circuit is completely concretized, except for input variables, which we will explain in a later section.

## The extraction driver

The central object is `ExtractionDriver`, which implements Ragu's `Driver` interface.
Its goal is to record symbolic operations emitted by the circuit.
The driver sets `MaybeKind = Empty`, so circuit generation proceeds without computing concrete witness data.
The driver also sets the wire type to be a symbolic expression, that is, `ImplWire = Expr<F>`.

The important driver methods map Ragu synthesis steps into operations as follows:

- `alloc` allocates one fresh wire and records `Op::Witness { count: 1 }`.
- `mul` allocates three fresh wires, records `Op::Witness { count: 3 }`, and then adds a constraint for `a * b - c = 0`.
- `add` does not allocate any wire and does not emit any operation. It returns a symbolic expression only.
- `enforce_zero` builds a symbolic expression and adds a constraint, enforcing it to be zero.
- `constant` returns a constant expression and does not emit any operation.

This driver implementation provides the core mapping from Ragu driver operations to `Clean` operations, so it is crucial that Ragu driver semantics is correctly converted into `Clean` circuit semantics.

## Expression logging

The symbolic language used by the driver is `Expr`.
It mirrors the shape of `Clean`'s `Expression` type:

- `Expr::Var` represents a variable in the witness,
- `Expr::InputVar` represents an input variable,
- `Expr::Const` represents a constant field element,
- `Expr::Add` and `Expr::Mul` build expression trees for addition and multiplication.

Variables are referenced by their index, starting at `1`.
The index `0` has special meaning, and is always reserved for the `ONE` wire, containing the constant field element `1`.
Variables are allocated contiguously, mimicking the circuit model of `Clean`.

## Mapping into `Clean` operation semantics

After synthesis, the driver holds a flat list of `Op::Witness` and `Op::Assert`.
The exporter translates that list directly into `Clean` `Operation`s.

- `Op::Witness { count }` translates to `Operation.witness count (fun _env => default)`.
- `Op::Assert e` translates to `Operation.assert e`.

The witness computation function is replaced by `default`, because the extracted artifact is used to reason about the allocated variables and asserted relations, not to recover the original Rust witness-generation code.

The exported Lean code therefore has the form:

```lean
def exported_operations (input_var : Var Inputs CircuitField) : Operations CircuitField := [
  Operation.witness count (fun _env => default),
  Operation.assert expr,
  ...
]
```
