# Linear Expressions

[`enforce_zero()`] and [`add()`] both work with linear combinations of wires.
Drivers define their own [`Wire`] types so they can represent wires efficiently
to suit their execution context. For the same reason, evaluating a linear
combination $c_1 w_1 + c_2 w_2 + \cdots$ can look very different depending on
the driver: one might accumulate a field element, and another might fold each
term's contribution into polynomial coefficients. Circuit code shouldn't have to
build a `Vec<(Coeff, Wire)>` and hand it off, which would force an intermediate
allocation that drivers don't usually need.

The [`LinearExpression`] trait solves this with a builder-pattern API: the
driver supplies an empty expression of its own concrete type, circuit code
chains terms onto it incrementally, and it processes each term on the spot, with
no intermediate collection required.

## The Closure Pattern {#the-closure-pattern}

[`add()`] and [`enforce_zero()`] accept closures so drivers that don't need the
result can avoid building the expression altogether. Drivers that do track
constraints call the closure with an empty expression of their own concrete
type, and circuit code builds on it using only the [`LinearExpression`] trait
methods.[^hidden-types]

The central implementation method is [`add_term`], which appends a wire with an
explicit [`Coeff<F>`] coefficient. [`Coeff<F>`] is an enum whose variants let
drivers select cheaper code paths for common coefficient patterns instead of
always performing a full field multiplication. The convenience methods [`add`],
[`sub`], and [`extend`] delegate to [`add_term`] by default.

Here, an `enforce_zero` call constrains the elliptic curve equation $x^3 + b -
y^2 = 0$, where `x3` holds $x^3$ and `y2` holds $y^2$:

```rust,ignore
dr.enforce_zero(|lc| {
    lc.add(x3.wire())
        .add_term(&D::ONE, Coeff::Arbitrary(C::b()))
        .sub(y2.wire())
})?;
```

## Virtual Wires {#virtual-wires}

Unlike [`enforce_zero()`], the [`add()`] method does not create a constraint. It
returns a **virtual wire** representing the linear combination described by the
closure. Because the combination is substituted inline wherever the wire appears
in later constraints, virtual wires are free: they do not add gates to the
circuit.

This matters for gadgets like [`Point`]. During point addition, the result
coordinates are linear combinations involving the input coordinates alongside
intermediate values, and each arithmetic step adds more terms. Without virtual
wires, [`Point`] would have to carry those growing expressions explicitly; a
scalar multiplication would make this unmanageable.

Virtual wires solve this by offloading the bookkeeping to the driver. Each call
to [`add()`] offers the driver a linear combination and receives an opaque wire
in return. A constraint-tracking driver records the combination and resolves it
when the wire appears in later constraints; other drivers can return a wire
backed by the evaluated field element alone.

## Gain

Every linear expression carries a **gain** factor, initialized to $1$. The
[`gain`] method multiplies the current gain by a given [`Coeff<F>`]; all terms
added after a gain change incorporate the updated gain, while earlier ones are
left untouched.

One typical use of gain is binary decomposition (packing Boolean bits into a
field element). The [`multipack`] routine packs a slice of [`Boolean`] wires
into a single field element by adding each bit and doubling the gain after every
step. Starting from gain $1$, the first bit contributes $b_0$, the second $2
b_1$, the third $4 b_2$, and so on — producing $b_0 + 2 b_1 + 4 b_2 + \cdots$
naturally.

```admonish info
This forward-only design is deliberate. A retroactive `scale`, while being more
familiar, would require every driver to revisit earlier terms, which not all can
do cheaply. Nor can circuit code approximate gain by pre-multiplying
coefficients before [`add_term`]: some drivers multiply each coefficient by an
internal factor inside [`add_term`], so pre-multiplying would duplicate that
per-term arithmetic. [`gain`] avoids both problems by letting the driver fold
the caller's scaling into its own bookkeeping once, so later terms inherit the
factor automatically.
```

[^hidden-types]: Because closures carry concrete parameter types, the driver
    cannot hide its expression type: Rust requires it to appear somewhere in the
    trait hierarchy as the [`LCadd`] and [`LCenforce`] associated types, even though
    circuit code never refers to them by name.

[`LinearExpression`]: ragu_core::drivers::linexp::LinearExpression
[`add`]: ragu_core::drivers::linexp::LinearExpression::add
[`sub`]: ragu_core::drivers::linexp::LinearExpression::sub
[`add_term`]: ragu_core::drivers::linexp::LinearExpression::add_term
[`extend`]: ragu_core::drivers::linexp::LinearExpression::extend
[`gain`]: ragu_core::drivers::linexp::LinearExpression::gain
[`Coeff<F>`]: ragu_arithmetic::Coeff
[`LCadd`]: ragu_core::drivers::DriverTypes::LCadd
[`LCenforce`]: ragu_core::drivers::DriverTypes::LCenforce
[`Wire`]: ragu_core::drivers::Driver::Wire
[`add()`]: ragu_core::drivers::Driver::add
[`enforce_zero()`]: ragu_core::drivers::Driver::enforce_zero
[`multipack`]: ragu_primitives::boolean::multipack
[`Boolean`]: ragu_primitives::boolean::Boolean
[`Point`]: ragu_primitives::point::Point
