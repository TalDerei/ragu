# [`GadgetKind`][gadgetkind-trait]

The [`Gadget`][gadget-trait] trait is defined as

```rust
pub trait Gadget<'dr, D: Driver<'dr>>: Clone {
    // ...
}
```

so that any concrete [`Gadget`][gadget-trait] must be parameterized by a
concrete [`Driver`][driver-trait]. But because gadgets can be transformed
between drivers, a higher-kinded interface is used to describe the
driver-agnostic type information and behavior of a gadget. This is done
through the [`GadgetKind<F>`][gadgetkind-trait] trait, which is defined as

```rust
pub unsafe trait GadgetKind<F: Field>: core::any::Any {
    type Rebind<'dr, D: Driver<'dr, F = F>>: Gadget<'dr, D, Kind = Self>;

    // ...
}
```

where the generic associated type `Rebind<'dr, D>` allows an implementation
of [`GadgetKind`][gadgetkind-trait] to specify how a concrete
[`Gadget`][gadget-trait] type can be obtained from a concrete
[`Driver`][driver-trait]. The [`Gadget`][gadget-trait] trait, in turn, has an
associated type `Kind` that relates back to its corresponding
[`GadgetKind`][gadgetkind-trait] implementation.

## The `Bound` Type Alias

The [`Bound<'dr, D, K>`][bound-alias] type alias is shorthand for
`<K as GadgetKind<F>>::Rebind<'dr, D>`.

## `map_gadget` {#map-gadget}

[`GadgetKind::map_gadget`](ragu_core::gadgets::GadgetKind::map_gadget)
translates a gadget from one driver to another, walking its fields and
converting wires and witness data to the destination driver. See
[Conversion](conversion.md) for details.

This traversal is part of the gadget's contract. It must visit wire fields in
the same order for every instance of the same concrete gadget type, defining
which wires correspond between instances. [Fungibility](index.md#fungibility)
is stated in terms of this correspondence, and drivers and internal Ragu code
use it to count, substitute, or extract wires.

## `enforce_conservative_equal_gadget`

Gadgets implement the
[`GadgetKind::enforce_conservative_equal_gadget`][enforce-equal] method to
specify conservative equality constraints by pairing corresponding wires in the
gadget's canonical traversal. This is the raw fallback used where a gadget's
invariants are *not* guaranteed to hold, so the contract is strict: it must
constrain each pair of corresponding wires and do nothing else — no extra gates,
no arbitrary constraints, and no invariant-aware equality shortcuts.

To make that contract enforceable at the type level rather than by convention,
the method does not receive a full [`Driver`][driver-trait]. Instead it is
handed a [`WireEqualizer`][wire-equalizer] — a restricted view over the driver
whose only operation is
[`enforce_conservative_equal`][wire-equalizer-method] over a wire pair.
Composite gadgets thread the same `WireEqualizer` into their subgadgets via
[`Gadget::enforce_conservative_equal_with`][enforce-equal-with], and the derive
macro generates exactly these calls.

Most circuit code should avoid this path directly. Prefer
[`GadgetExt::enforce_equal`][gadgetext-enforce-equal], backed by
[`GadgetEquals`][gadget-equals], for ordinary gadget comparisons — it may
constrain fewer wires by relying on a gadget's invariants. Conservative equality
is reserved for infrastructure such as consistency checks and wire-substitution
paths, which must re-establish constraints without trusting any prior invariant.

## Safety

Notice that the [`Gadget`][gadget-trait] trait is safe to implement, but the
[`GadgetKind`][gadgetkind-trait] trait is not. All gadgets must implement both
traits, but it is the [`GadgetKind`][gadgetkind-trait] trait that imposes a
memory-safety requirement on the types that implement it: gadgets must implement
`Send` if their wires are `Send` as well. This is impossible to express in
today's Rust type system, which is why the trait is `unsafe`.

```admonish warning
The `Send` requirement is the **only** safety invariant that
[`GadgetKind`][gadgetkind-trait] imposes.
[Fungibility](index.md#fungibility) — the requirement that gadget behavior
be fully determined by its type — is a separate correctness contract
documented on the [`Gadget`][gadget-trait] trait. Violating fungibility may
produce incorrect circuits but does not cause undefined behavior.
```

However, due to the complexity of the API contract we generally need to
[automatically derive](index.md#automatic-derivation) the
[`Gadget`][gadget-trait] and [`GadgetKind`][gadgetkind-trait] traits anyway.
The [`GadgetKind`][gadgetkind-trait] trait gives us the ability to stuff the
scary `unsafe` keyword into a corner of the API where users don't need to
see it.

[gadget-trait]: ragu_core::gadgets::Gadget
[gadgetkind-trait]: ragu_core::gadgets::GadgetKind
[bound-alias]: ragu_core::gadgets::Bound
[driver-trait]: ragu_core::drivers::Driver
[enforce-equal]: ragu_core::gadgets::GadgetKind::enforce_conservative_equal_gadget
[enforce-equal-with]: ragu_core::gadgets::Gadget::enforce_conservative_equal_with
[wire-equalizer]: ragu_core::gadgets::WireEqualizer
[wire-equalizer-method]: ragu_core::gadgets::WireEqualizer::enforce_conservative_equal
[gadgetext-enforce-equal]: ragu_primitives::GadgetExt::enforce_equal
[gadget-equals]: ragu_primitives::comparison::GadgetEquals
