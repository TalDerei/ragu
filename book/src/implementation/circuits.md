# Circuits

The [`ragu_circuits`] crate turns arithmetic circuit definitions into
polynomials. For the underlying protocol-level arithmetization see the
[arithmetization chapter](../protocol/core/arithmetization.md); for the
multi-stage extension layered on top see the
[staging implementation](staging.md).

## The `Circuit` Trait

[`Circuit<F>`][circuit-trait] is the core abstraction. Any type that
implements it declares an `Instance` type (public data the verifier
possesses), a `Witness` type (secret data the prover supplies), an
`Output` type serialized into the $k(Y)$ instance polynomial, and an
`Aux` type for auxiliary data useful in future synthesis passes.

Two methods reflect each other.
[`instance`][circuit-instance] derives the expected output from public
data alone; [`witness`][circuit-witness] performs the full computation
and returns both the output gadget and any auxiliary data. Both take a
[`Driver`], the same circuit code runs whether the driver is counting
constraints, evaluating the wiring polynomial, or computing a real
trace.

[`CircuitExt`][circuit-ext] is blanket-implemented for every
`Circuit<F>`. Its [`trace`][circuit-trace] method runs `witness` on an
evaluating driver to produce a [`Trace`] of raw gate values; its
[`ky`][circuit-ky] method evaluates the instance polynomial $k(y)$ at a
concrete challenge $y$.

## `Maybe<T>`

Circuit code runs under drivers that may or may not need concrete
values. `Maybe<T>` resolves this at the type level: drivers with
`Always` carry real values, while drivers with `Empty` use a
zero-sized stand-in and never execute value-producing closures. This
lets the same circuit code serve witness generation, instance
evaluation, metrics, and wiring evaluation without runtime branching.

## Witness Structure

The prover's witness $\v{r}$ is defined by
$\v{a}, \v{b}, \v{c}, \v{d} \in \F^n$, where $n = 2^k$. Individual
elements are known as _wires_, specifically _allocated_ wires, because
the prover must commit to them and they exist at a cost. They are called
"wires" rather than "variables" because they principally behave as
inputs and outputs to multiplication gates. Each gate enforces
$\v{a}_i \v{b}_i = \v{c}_i$ and
$\v{c}_i \v{d}_i = 0$. The fourth wire $\v{d}$ defaults to zero, with
$\v{d}_0 = 1$ reserved for the `ONE` wire; non-system $\v{d}$ slots
may carry witness values when their gate's $\v{c}_i = 0$ makes the
second equation vacuous.

The witness $\v{r}$ is the concatenation
$\v{c} \| \rv{a} \| \v{b} \| \rv{d}$, a
[structured polynomial](../protocol/local/arithmetization.md).

### Virtual Wires

The left-hand side of each constraint is a linear combination of
elements within $\v{a}, \v{b}, \v{c}, \v{d}$. Any linear combination of wires
can itself be considered a _virtual_ wire (as opposed to an allocated
wire) which imposes no cost on the protocol.

### `ONE`

The `ONE` wire $\v{d}_0 = 1$ is provided by the SYSTEM gate at
position 0. The verifier sets $\v{k}_0 = 1$, and the
[wiring polynomial](../protocol/local/wiring.md) satisfies
$s(X, 0) = 1$.

## Trace and Segments

[`Trace`] holds the gate values produced by synthesis as a list of
_segments_, groups of four dense vectors $(a, b, c, d)$ corresponding
to multiplication-gate wire assignments.

Segment 0 is the _root_: all gates allocated outside of routine calls,
plus the SYSTEM gate at position 0. Each `Driver::routine` call creates
an additional segment isolated from its parent's gate indices. Segments
are ordered by DFS traversal of the routine call tree. Under the
`multicore` feature, subtrees run in parallel; each is annotated with a
DFS path and the results are sorted back into DFS order before
assembly.

## Metrics and Fingerprinting

Before any trace is computed, the circuit's constraint topology is
analyzed by running synthesis on a counting driver. The result is a
`CircuitMetrics`: total gate and constraint counts, plus a
[`SegmentRecord`] for each segment in DFS order.

Each routine invocation produces a [`RoutineFingerprint`], a
Schwartz-Zippel fingerprint that combines the Rust `TypeId` of the
routine's input and output types, a scalar evaluation of the routine's
$s(X, Y)$ contribution at deterministic pseudorandom points, and the
local gate and constraint counts. Two routines sharing a fingerprint
have identical constraint shapes with probability ~$1 - 2^{-64}$.

[`RoutineIdentity`] wraps the fingerprint to distinguish the root
segment (which cannot be memoized) from actual routine invocations.

## Floor Planning

The floor planner converts per-segment counts into absolute offsets.
[`floor_plan`][floor-plan-fn] takes segment records from metrics and
returns [`ConstraintSegment`] entries, each specifying `gate_start`
(the absolute gate index) and `constraint_start` (the absolute
$Y$-power index for the segment's first constraint).

The current layout is a simple prefix sum: segments are placed
contiguously in DFS order. Routines with matching fingerprints have
identical constraint shapes, which a future floor planner could exploit
to assign congruent layouts and memoize $s(X, Y)$ evaluations.

## Synthesis Flow

The lifecycle of a circuit from definition to polynomial:

1. **Metrics.** Synthesis runs on a counting driver, producing
   `CircuitMetrics`.
2. **Registration.** The circuit and its metrics are registered with a
   [`Registry`][registry], which computes the floor plan and stores
   evaluable wiring objects for on-demand $s(X, Y)$ queries.
3. **Trace.** For a concrete witness, `CircuitExt::trace` produces a
   `Trace` of raw gate values.
4. **Assembly.** `Registry::assemble` scatters each trace segment to
   the absolute position assigned by the floor plan, producing the
   $r(X)$ [trace polynomial](../protocol/local/arithmetization.md).
5. **Polynomial evaluation.** The wiring and trace polynomials feed
   into the [protocol's verification checks](../protocol/core/nark.md).

For multi-stage circuits, stage polynomials are interleaved between
steps 3 and 4; see the [staging implementation](staging.md).

[`ragu_circuits`]: https://docs.rs/ragu_circuits/latest/ragu_circuits/
[circuit-trait]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.Circuit.html
[circuit-instance]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.Circuit.html#tymethod.instance
[circuit-witness]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.Circuit.html#tymethod.witness
[circuit-ext]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.CircuitExt.html
[circuit-trace]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.CircuitExt.html#method.trace
[circuit-ky]: https://docs.rs/ragu_circuits/latest/ragu_circuits/trait.CircuitExt.html#method.ky
[`Driver`]: https://docs.rs/ragu_core/latest/ragu_core/drivers/trait.Driver.html
[`Trace`]: https://docs.rs/ragu_circuits/latest/ragu_circuits/struct.Trace.html
[`SegmentRecord`]: https://docs.rs/ragu_circuits/latest/ragu_circuits/struct.SegmentRecord.html
[`RoutineFingerprint`]: https://docs.rs/ragu_circuits/latest/ragu_circuits/struct.RoutineFingerprint.html
[floor-plan-fn]: https://docs.rs/ragu_circuits/latest/ragu_circuits/floor_planner/fn.floor_plan.html
[`ConstraintSegment`]: https://docs.rs/ragu_circuits/latest/ragu_circuits/floor_planner/struct.ConstraintSegment.html
[`RoutineIdentity`]: https://docs.rs/ragu_circuits/latest/ragu_circuits/enum.RoutineIdentity.html
[registry]: https://docs.rs/ragu_circuits/latest/ragu_circuits/registry/struct.Registry.html
