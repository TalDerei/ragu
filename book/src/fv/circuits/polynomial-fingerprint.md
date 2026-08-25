# Direct Randomized Polynomial Equivalence Check

The deterministic [trace fingerprint](./fingerprint.md) remains useful for
exact diagnostics, but its Rust side first builds an `ExtractionDriver`
expression trace. The direct randomized check removes that trace from the
primary comparison path:

```text
fresh CI seed
  |-- Rust: production gadget -> EvaluationDriver -> evaluation record
  `-- Lean: FormalInstance reimplementation -> Clean expressions -> evaluation record
                                                        |
                                                     exact diff
```

The two sides share the versioned evaluation specification, seed, instance
name, field, and number of points. Lean does not consume the Rust trace or the
Rust evaluation. Each side runs its own circuit model and computes its own
record.

## What Rust evaluates

`CircuitInstance::circuit` is generic over the small `FvDriver` extension of
Ragu's production `Driver` API. The same function can therefore run with either
the symbolic `ExtractionDriver` or the direct `EvaluationDriver`.

The direct driver uses field elements as wires. It assigns challenge values to
inputs and to all four production gate slots `(A, B, C, D)`, immediately
evaluates linear combinations, and records both production gate relations:

```text
A * B - C = 0
C * D     = 0
```

An `Extra` token carries the corresponding `D` value. `assign_extra` consumes
that token and records which `D` slot was used. No symbolic Rust expression DAG
is constructed on this path, and witness-producing closures are not called.

## What Lean evaluates

Lean instantiates the handwritten `FormalInstance.reimplementation` with
canonical symbolic inputs and obtains its flattened Clean operations and output
expressions. It then independently derives the challenge values and recursively
evaluates the Lean `.var`, `.const`, `.add`, and `.mul` expressions.

The current bridge decodes each three-variable witness immediately followed by
an assertion as one production gate. The three variables are `A`, `B`, and `C`;
the actual Lean assertion is evaluated as the first gate relation, and Lean
reconstructs a fresh `D` slot and `C * D` as the second relation. Lean
normalizes each gate assertion and requires it to be exactly `A * B - C`; every
remaining assertion and output must have ordinary variable degree at most one,
matching the production driver's linear-expression API. Lookups, interactions,
other witness shapes, out-of-range variables, and nonlinear expressions fail
closed.

None of the 53 currently enrolled isolated gadget instances calls
`assign_extra`; their exact header therefore records zero extra assignments.
The Rust driver has direct synthetic coverage of `D`, `C * D`, and
`assign_extra`. If an enrolled instance begins using an extra slot before the
Lean representation is extended to identify its originating `D`, the
cross-language check fails rather than silently omitting it.

## Challenge derivation

The format and domain separator are `ragu-fv-polynomial-v1`. For each field,
instance, evaluation point, and label, both implementations form:

```text
"ragu-fv-polynomial-v1"        raw ASCII
seed                            32 bytes
modulus                         32-byte little-endian integer
len(instance) ++ instance       u64 little-endian length, then UTF-8
point                           u64 little-endian
len(label) ++ label             u64 little-endian length, then ASCII
block                           one byte: 0 or 1
```

They compute SHA-256 once with `block = 0` and once with `block = 1`, concatenate
the two digests, interpret the 64 bytes as a little-endian integer, and reduce
it modulo the field. This is hash-to-field, not hash-to-curve.

The labels are:

```text
input
wire-a, wire-b, wire-c, wire-d
gate-ab-weight, gate-cd-weight
constraint-weight, extra-weight, output-weight
```

If a label's derived field element is `r`, position `i` receives
`r^(i + 1)`. Using geometric sequences keeps evaluation linear in circuit size
while preserving the order of every slot and relation.

Two fixed Rust and Lean unit vectors pin this byte-level transport for the
Pallas and Vesta fields. CI supplies a new seed only after the revision has
been checked out, and prints the non-secret seed so a failure can be replayed.

## Accumulators

For gate index `g`, constraint index `j`, assigned-extra index `k`, and output
index `l`, each point contains four field elements:

```text
G = sum_g u_g * (A_g * B_g - C_g) + v_g * (C_g * D_g)
L = sum_j s_j * constraint_j
E = sum_k t_k * assigned_D_k
O = sum_l z_l * output_l
```

The weights `u`, `v`, `s`, `t`, and `z` come from their separately
domain-separated geometric sequences. Counts and arities are compared exactly;
only equality of the four field accumulators is probabilistic.

## Degree and false-accept bound

Geometric substitution turns each accumulator into a multivariate polynomial
in the domain-separated bases. If a record has `i` inputs, `g` gates, `c`
linear constraints, `e` assigned extras, and `o` outputs, the declared
conservative total-degree bound is:

```text
v = max(i, g)
d = max(3*g, v+c, g+e, v+o)
```

Lean first checks the canonical-gate and linear-expression restrictions, then
computes the geometric degree of its actual expressions and rejects the model
if it exceeds this structural bound. Both sides reject `d > 2048`. The largest
current instance is `Ragu.Instances.Poseidon.Blocks2Squeeze3Fp`, with
`d = 1728`.

For a nonzero polynomial of degree at most `d`, Schwartz--Zippel bounds an
accidental zero by `d` times the maximum mass of one challenge value
(Schwartz, <a href="https://pages.cs.wisc.edu/~cs787-1/Schwartz1980.pdf">Fast
Probabilistic Algorithms for Verification of Polynomial Identities</a>, JACM
1980). The Lean accounting includes the slight nonuniformity from reducing 512
random bits modulo the field: one field element has at most

```text
ceil(2^512 / |F|) / 2^512
```

mass. With `d <= 2048` and two independently domain-separated evaluation
points, `pastaFp_two_point_prob_le` and `pastaFq_two_point_prob_le` prove the
numeric bound is below `2^-480` for both Pasta fields.

This probability statement assumes the two SHA-256 blocks for every distinct
domain are independent random-oracle outputs and that a disagreement produces
a nonzero polynomial within the checked degree bound. The Lean theorems check
the arithmetic bound; they do not formalize SHA-256 as a random oracle or prove
the Rust/Lean semantic correspondence.

## Record format

Each instance prints one tab-separated line:

```text
format tag
seed (64 lowercase hex digits)
fully qualified instance name
modulus (64 big-endian hex digits)
input count
output count
gate count
gate-relation count
linear-constraint count
assigned-extra count
degree bound
point count
point evaluations
```

One point evaluation is `G,L,E,O`, with each field element encoded as 32
little-endian bytes in lowercase hexadecimal. Multiple points are separated by
semicolons. The header is an exact comparison and must be identical at every
point.

## Assurance boundary

For every enrolled isolated gadget, the check binds the production-driver
view of:

- input/output arity and output order;
- all `A`, `B`, `C`, and `D` gate slots and both gate relations;
- ordered linear constraints;
- ordered `assign_extra` use on the Rust side, failing closed until represented
  on the Lean side; and
- both Pasta fields.

It does not cover witness values or witness-generation closures. It also does
not establish the backend's floor plan, backend-specific system gates outside
the `Driver` contract, routine boundaries, shared allocator state and wiring in
the deployed composed circuit, or verifier acceptance behavior. Those require
a separate composed-circuit deployment check, tracked in
[#865](https://github.com/tachyon-zcash/ragu/issues/865). Gadget contracts
establish Lean proof composition; this randomized check establishes the
gadget-level Rust-to-Lean binding.

## Running it

Use an explicit 32-byte seed:

```text
cargo run --locked -p lean_extraction -- polynomial-fingerprint \
  --seed <64-hex-digit-seed> --points 2

cd qa/fv
lake env lean --run Ragu/PolynomialFingerprint/Main.lean \
  <64-hex-digit-seed> 2
```

Sort and diff the two outputs. There is deliberately no implicit seed.
