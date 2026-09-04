# Direct Randomized Polynomial Equivalence Check

The [trace fingerprint](./fingerprint.md) diffs an `ExtractionDriver`
expression trace and remains the tool for exact diagnostics. This check keeps
no trace on the primary path: from one seed, Rust evaluates the production
gadget under an `EvaluationDriver` and Lean evaluates its
`FormalInstance.reimplementation`, each producing a record that must diff
clean. The sides share only the versioned specification, the seed, the
instance name, the field, and the point count.

## The two evaluators

`CircuitInstance::circuit` is generic over `InstanceDriver`, a one-method extension
of the production `Driver` API, so the same gadget body runs under the
symbolic `ExtractionDriver` or the direct `EvaluationDriver`. The direct
driver uses field elements as wires: it assigns challenges to the inputs and
to all four gate slots `(A, B, C, D)`, evaluates linear combinations
immediately, and records both gate relations, `A * B - C = 0` and
`C * D = 0`. An `Extra` token carries `D`; `assign_extra` consumes it and
records the slot. No expression DAG is built and no witness closure runs.

Lean evaluates its Clean expressions on canonical symbolic inputs with the
same challenges. Each three-variable witness followed by an assertion is one
gate: the normalized assertion must be exactly `A * B - C`, and Lean
reconstructs a fresh `D` for `C * D`. Every other assertion and output must be
linear in the variables, as the production API is; lookups, interactions,
other witness shapes, out-of-range variables, and nonlinear expressions fail
closed. No enrolled instance calls `assign_extra` yet (the Rust driver covers
it synthetically); if one does, the check fails until Lean can identify the
originating `D`.

## Challenges and accumulators

Under the domain separator `ragu-fv-polynomial-v1`, each challenge is
SHA-256 over the tag, the 32-byte seed, the little-endian modulus, the
length-prefixed instance name, the `u64` point index, the length-prefixed
label, and a block byte; the digests for blocks `0` and `1` are concatenated
and reduced modulo the field. Labels are `input`; `wire-a` to `wire-d`;
`gate-ab-weight`, `gate-cd-weight`; and `constraint-weight`, `extra-weight`,
`output-weight`. Position `i` under a label with element `r` receives
`r^(i + 1)`, keeping evaluation linear in circuit size and every slot in
order. Fixed unit vectors pin the byte transport for both Pasta fields; CI
draws a fresh seed after checkout and prints it for replay.

Per point, over gates `g`, linear constraints `j`, assigned extras `k`, and
outputs `l`:

```text
G = sum_g u_g * (A_g * B_g - C_g) + v_g * (C_g * D_g)
L = sum_j s_j * constraint_j
E = sum_k t_k * assigned_D_k
O = sum_l z_l * output_l
```

Counts and arities are compared exactly; only these four field elements are
probabilistic.

## False-accept bound

With `i` inputs, `g` gates, `c` linear constraints, `e` assigned extras, and
`o` outputs, the declared total degree is `d = max(3g, v + c, g + e, v + o)`
for `v = max(i, g)`. Lean checks its actual expressions against this bound
and both sides reject `d > 2048`; the largest enrolled instance,
`Poseidon.Blocks2Squeeze3Fp`, has `d = 1728`. By Schwartz--Zippel
([Schwartz 1980](https://pages.cs.wisc.edu/~cs787-1/Schwartz1980.pdf)) a
nonzero polynomial of degree `d` vanishes at a random point with probability
at most `d` times one challenge value's maximum mass,
`ceil(2^512 / |F|) / 2^512`; with two independently separated points,
`pastaFp_two_point_prob_le` and `pastaFq_two_point_prob_le` prove this is
below `2^-480` for both Pasta fields. The theorems establish the arithmetic
only: SHA-256 as a random oracle and the Rust/Lean semantic correspondence
are assumptions.

## Record and assurance boundary

Each instance prints one tab-separated line: format tag, seed, instance
name, modulus, the input/output/gate/gate-relation/constraint/extra counts,
degree bound, point count, and per-point `G,L,E,O` as little-endian hex.
The header must match exactly at every point.

For every enrolled isolated gadget this binds the production-driver view of
input/output arity and order, all four gate slots and both relations, the
ordered linear constraints, ordered `assign_extra` use, and both Pasta
fields. It does not cover witness values or witness closures, the backend's
floor plan or system gates outside the `Driver` contract, routine
boundaries, allocator state and wiring in the composed circuit, or verifier
acceptance; those need a composed-circuit deployment check, tracked in
[#865](https://github.com/tachyon-zcash/ragu/issues/865). Gadget contracts
establish Lean proof composition; this check establishes the gadget-level
Rust-to-Lean binding.

## Running it

```text
cargo run --locked -p lean_extraction -- polynomial-fingerprint \
  --seed <64-hex-digit-seed> --points 2

cd qa/fv
lake env lean --run Ragu/PolynomialFingerprint/Main.lean \
  <64-hex-digit-seed> 2
```

Sort and diff the two outputs. There is deliberately no implicit seed.
