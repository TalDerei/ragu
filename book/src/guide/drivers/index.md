# Drivers

Ragu requires the same algorithms to execute both natively—where only the
computation’s result matters—and as arithmetic circuits describing the same
computation. The protocol’s non-uniform design amplifies this: there is no
one-time preprocessing step, so circuit code is also evaluated in additional
settings for algebraic or structural manipulation, where only a subset of the
usual synthesis machinery is needed. Maintaining separate implementations across
these contexts would quickly become untenable.

The **[`Driver`]** trait eliminates this duplication: we write circuit code
once, generic over a driver, and concrete drivers specialize their
interpretation for each context. In particular, drivers can choose wire
representations and gate expensive work (such as witness assignment) so contexts
don’t pay for unused machinery, often through compile-time specialization.

## The [`Driver`] Trait {#driver-trait}

Circuit code is written generically over a type `D: Driver<'dr>`, receiving the
driver as a mutable reference `dr: &mut D`. The driver is stateful: as circuit
code calls its methods, it accumulates wires, constraints, and internal
bookkeeping. The mutable reference is the sole interface between circuit code
and the synthesis context it runs in.

The driver exposes three core operations:

* [`mul()`]: returns wires $(a, b, c)$ with the initial constraint $a \cdot b =
      c$. This operation simultaneously _assigns_ them values: `mul` is called
      with a closure that returns the three value assignments for the new wires.
      The closure is evaluated only in contexts where assignments are required.
* [`enforce_zero()`]: enforces that a linear combination of previously created
      wires equals zero. This operation takes a closure that is only executed
      when the driver needs to know about the constraint system. The closure is
      used to [build the linear combination](linear.md#the-closure-pattern) in a
      way that suits the driver's needs and optimization opportunities.
* [`add()`]: returns a new _virtual_ wire representing a linear combination of
      previously created wires. See [Virtual Wires](linear.md#virtual-wires) for
      more on how this works and why it matters.

There are also some helpful utilities made available by all drivers. The
associated [`ONE`] constant is a wire that is fixed to the value $1$, and is
available everywhere. The [`constant()`] method is a simple helper that returns
a virtual wire assigned to a constant, which is free because it is a virtual
wire that scales [`ONE`].

### Allocation

Sometimes only a single wire is needed, but [`mul()`] always allocates three. To
support single-wire allocation, drivers provide an additional [`alloc()`] method
that allocates and assigns one wire.

By default, `alloc` calls `mul`, returns the $a$ wire, and sets the
corresponding $b$ and $c$ wires to zero to satisfy the multiplication
constraint—wasting $b$ and $c$. Drivers may override `alloc` to avoid this
overhead. For example, synthesis drivers return the $a$ wire from a `mul`
operation, stash the associated $b$ wire for the next `alloc` call, and fill in
$c$ later to satisfy the constraint.

### The `'dr` Lifetime

Drivers are parameterized by a special `'dr` lifetime that enables efficient
borrowing throughout circuit code. Without it, the trait's associated types
would carry an implicit `'static` bound, and every reference would have to be
replaced with reference counting.

The lifetime lets a driver's `Wire` type hold a plain reference into the
driver's backing storage. It also propagates into witness and instance methods,
so circuits (and [gadgets](../gadgets/index.md)) can borrow their input data
rather than requiring callers to clone or wrap it in `Arc`.

```admonish info
`'dr` also enables zero-cost scoped parallelism for [`Routine`]s. The trait's
predict/execute split and `Aux<'dr>` associated type are scaffolding for a
driver that dispatches routine execution to worker threads: binding `'dr` to the
thread scope's lifetime lets routines hold borrowed references and send auxiliary
data to workers without `Arc`.
```

### Equality

The [`enforce_equal()`] method constrains two wires to have the same value. By
default it calls [`enforce_zero()`] on their difference, but drivers may
override it.

## Concrete Drivers

Ragu uses drivers internally to execute circuit code, and users do not need to
implement or directly interact with drivers except in advanced use cases or test
code. The most useful drivers that are exposed in the public API are:

* [Emulators](../../implementation/drivers/emulator.md) execute circuit code
  without enforcing constraints, which is useful when only the correct result is
  desired and the actual machinery of the arithmetic circuit reduction is
  irrelevant.
* [`Simulator`] (in `ragu_primitives`) also executes circuit code but _does_
  enforce constraints and collects realistic metrics in the process, which is
  useful for testing.

[`mul()`]: ragu_core::drivers::Driver::mul
[`enforce_zero()`]: ragu_core::drivers::Driver::enforce_zero
[`add()`]: ragu_core::drivers::Driver::add
[`ONE`]: ragu_core::drivers::Driver::ONE
[`constant()`]: ragu_core::drivers::Driver::constant
[`alloc()`]: ragu_core::drivers::Driver::alloc
[`Driver`]: ragu_core::drivers::Driver
[`Routine`]: ragu_core::routines::Routine
[`Simulator`]: ragu_primitives::Simulator
[`enforce_equal()`]: ragu_core::drivers::Driver::enforce_equal
[`Wire`]: ragu_core::drivers::Driver::Wire
