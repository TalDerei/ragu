# Circuit under-constraint analysis checklist

Target pipeline:

`source AST linting -> witness-free source-shape linting -> circuit synthesis -> graph/connectivity/rank checks -> patcher fuzzing -> concrete-witness validation`

The stages are complementary. The AST pass is true no-execution source static
analysis. Source-shape linting abstractly executes generic circuit code without
witness values. Synthesis creates the constraint IR inspected by structural
graph analysis and witness-local rank analysis; patching is structure-aware
grey-box fuzzing; replay is dynamic validation.

## 1. Source AST linting

- [x] Parse every production crate source file with `syn`, without compiling or
  executing circuit code.
- [x] Reject discarded fallible driver/gadget results that bypass `?`, matching,
  or explicit error handling (`RAGU001`).
- [x] Reject witness-assignment closures that mutate captured state
  (`RAGU002`).
- [x] Reject witness-tainted conditions or loop bounds that control driver or
  gadget operations (`RAGU003`).
- [x] Review explicitly discarded constraint values and branches with different
  syntactic operation shapes (`RAGU004`/`RAGU005`).
- [x] Keep reviewed exceptions as line- and rule-specific source suppressions,
  with a rationale adjacent to each one; reject stale suppressions (`RAGU006`).
- [x] Run the strict no-advisory gate in Rust CI and `just lint`.
- [ ] Add macro-expanded, type-resolved HIR/MIR def-use and interprocedural
  taint analysis for aliases and helper calls that syntax alone cannot resolve.
- [ ] Add machine-readable circuit intent annotations before claiming that a
  missing `enforce_*` call is detectable in general; neither AST nor MIR can
  infer an unstated intended relation.

Implementation and rule documentation live in
[`qa/circuit-lint`](../circuit-lint/README.md).

## 2. Witness-free source-shape linting

- [x] Execute generic circuit code with a witness-free `Empty` driver, so
  witness-assignment closures cannot run.
- [x] Record exact wire ids, coefficients, gates, linear definitions,
  constraints, and public-output wires.
- [x] Require that shape to equal the concrete `Recorder` capture, not merely
  have the same event counts.
- [x] Pin a planted witness-dependent/swallowed-error regression that the lint
  must reject.
- [x] Run the lint over every captured production recursion circuit before a
  fuzz campaign starts.
- [x] Keep this driver-level abstract interpretation separate from the
  no-execution AST lint above.

## 3. Circuit synthesis

- [x] Capture every `Gate`, assigned `Extra`, virtual `Lin`, and `Enforce`
  event with its honest values.
- [x] Overlay committed stage values for `MultiStage` circuits and recompute
  virtual wires.
- [x] Refuse a capture whose honest witness does not satisfy the recorded
  graph.
- [x] Identify declared instance/stage inputs and watched outputs through each
  internal circuit's `CircuitSpec`.

## 4. Graph, connectivity, and rank checks

- [x] Treat wires as vertices and each event as a hyperedge.
- [x] Keep the fixed ONE wire as an anchor, not a universal bridge between
  otherwise independent subgraphs.
- [x] Retain allocated-but-unused wires as isolated singleton components.
- [x] Reject isolated wires and components that reach no declared input,
  output, or fixed constant in production captures.
- [x] Reject production output components with no path from any declared
  input.
- [x] Continue checking declared outputs with `forced_by`, both with inputs
  alone and with other hints granted.
- [x] Run exact Jacobian rank/nullity analysis on each component with at most
  384 derived wires; require nonzero checked coverage and no movable covered
  wire.
- [x] Report oversized components and their derived-wire counts as skipped;
  never interpret skipped rank coverage as a clean result.
- [x] Keep the existing whole-graph exact-rank oracle for generated patcher
  programs up to 384 wires.
- [ ] Add a scalable sparse/exact rank backend for large connected production
  components, eliminating the current dense-elimination cap.

## 5. Patcher fuzzing

- [x] Keep `fuzz_advice_patcher` for generated gadget programs with an
  independent native shadow.
- [x] Keep `fuzz_internal_circuits` for all five native recursion circuits and
  nested endoscaling steps at seeded, leaves, nodes, and lopsided points.
- [x] Let libFuzzer choose the circuit, distinct advice wires, and coordinated
  value mutations; repair derived wires through captured constraints.
- [x] Run a planted patcher self-test so an inert oracle fails loudly.
- [x] Keep the deterministic exhaustive single-wire sweep in
  `patcher_internal`, independent of libFuzzer.

## 6. Concrete-witness validation

- [x] Treat recorded-graph rejection as inconclusive, not a soundness signal.
- [x] When patching moves a watched output while inputs remain pinned, inject
  the candidate witness into a fresh synthesis of the same circuit.
- [x] Report a soundness signal only when fresh synthesis accepts it.
- [x] Report fresh-synthesis rejection separately as capture divergence.
- [x] Fail if the seeded replay cannot rebuild and reach the selected circuit.

## Verification

```sh
cargo run --locked -p ragu-circuit-lint -- --root . --deny-advisories
cargo test -p ragu_testing
cargo test -p ragu_pcd --features unstable-fuzzing --test patcher_internal
cd qa/fuzz
cargo test --lib
cargo check --bins
```

The first command is the no-execution source gate. The next two commands
exercise deterministic analyzers and sweeps. The last two compile the
libFuzzer harnesses without running a campaign; scheduled fuzz campaigns
provide the guided mutation search.
