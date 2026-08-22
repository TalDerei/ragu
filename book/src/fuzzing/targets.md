# Targets

The 24 targets, grouped by what they drive. Per-target detail lives in
`qa/fuzz/README.md`; this is the map.

## Op-stream

Random gadget programs over the [shared substrate](index.md).

| Target | Checks |
|---|---|
| `fuzz_element_ops` | Random compositions must not crash and must produce self-consistent witnesses. |
| `fuzz_witness_coverage` | The same, plus a witness-state hash spread over coverage branches to bias the search toward distinct internal states. |
| `fuzz_witness_cheat` | Swaps an element mid-stream for a fresh allocation of a different value, then compares fingerprints against the honest run. |
| `fuzz_driver_metamorphic` | `Simulator` and `Emulator<Wired<Fp>>` must assign the same wire values. |

## Under-constraint

Each starts from a satisfying witness, plants a cheat, and demands rejection.

| Target | Checks |
|---|---|
| `fuzz_witness_pinning` | Mutates one occupied trace-polynomial coefficient; the revdot identity must reject it. The circuit is made fully pinned, so a survivor means a wire nothing constrains. |
| `fuzz_circuit_cheat` | Mutates a witness input, re-traces, and compares the constraint verdict against a native oracle. |
| `fuzz_advice_patcher` | Mutates free advice wires and repairs through the *captured constraint graph* rather than gadget logic — which catches under-constrained advice that re-tracing would quietly fix. |
| `fuzz_completeness` | The other direction: arbitrary witnesses through anchorless circuits must all be accepted. |

## Gadget API

| Target | Checks |
|---|---|
| `fuzz_algebraic_identities` | Around sixteen gadget-level identities — commutativity, identities, distributivity, conditional select. |
| `fuzz_element_assertions` | Assertion gadgets accept valid inputs and reject invalid ones. |
| `fuzz_point_identities` | Group-law identities on the point gadget. |
| `fuzz_multipack` | Packing bits into elements round-trips. |
| `fuzz_consistent` | The `Consistent` invariants hold for arbitrary inputs. |
| `fuzz_io_roundtrip` | Gadget serialization round-trips through the IO buffer. |

## Primitives

| Target | Checks |
|---|---|
| `fuzz_poseidon_sponge` | Arbitrary absorb and squeeze sequences through the circuit sponge. |
| `fuzz_poseidon_differential` | Native and circuit sponges must agree. |
| `fuzz_endoscalar` | Endoscalar operations, with a special-scalar table of its own. |
| `fuzz_revdot` | The reverse-dot-product primitive. |
| `fuzz_fold_revdot` | Folding of the same. |
| `fuzz_sxy_agreement` | Registry consistency: $s(X, Y)$ must agree however it is evaluated. |

## Circuit pipeline

Full `witness` to `eval` to `assemble` pipelines, rather than gadget calls.

| Target | Checks |
|---|---|
| `fuzz_circuit_witness` | The witness pipeline against a native shadow, plus bespoke arms for gadget families the grammar does not generate — points, custom routines, known-prediction routines. |
| `fuzz_circuit_revdot_identity` | The canonical revdot identity over arbitrary generated circuits, in the accepting direction. |
| `fuzz_staging` | Per-stage and combined staging invariants, the final-mask check, and structural cross-mask bounds, across three stage shapes. |

## Verifier

| Target | Checks |
|---|---|
| `fuzz_verify_reject` | Corrupted proof bytes must be rejected. |
