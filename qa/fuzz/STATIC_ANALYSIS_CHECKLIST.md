# Circuit under-constraint analysis checklist

Target pipeline:

`source-shape linting -> circuit synthesis -> graph/connectivity/rank checks -> patcher fuzzing -> concrete-witness validation`

The stages are complementary. The first and third stages are white-box static
analysis; synthesis creates the constraint IR they inspect; patching is
structure-aware grey-box fuzzing; replay is dynamic validation.

## 1. Source-shape linting

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
- [ ] Add a general rustc AST/MIR lint for arbitrary Rust locals and missing
  API calls. The implemented pass is Ragu driver-level abstract interpretation,
  not a whole-language source analyzer.

## 2. Circuit synthesis

- [x] Capture every `Gate`, assigned `Extra`, virtual `Lin`, and `Enforce`
  event with its honest values.
- [x] Overlay committed stage values for `MultiStage` circuits and recompute
  virtual wires.
- [x] Refuse a capture whose honest witness does not satisfy the recorded
  graph.
- [x] Identify declared instance/stage inputs and watched outputs through each
  internal circuit's `CircuitSpec`.

## 3. Graph, connectivity, and rank checks

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

## 4. Patcher fuzzing

- [x] Keep `fuzz_advice_patcher` for generated gadget programs with an
  independent native shadow.
- [x] Keep `fuzz_internal_circuits` for all five native recursion circuits and
  nested endoscaling steps at seeded, leaves, nodes, and lopsided points.
- [x] Let libFuzzer choose the circuit, distinct advice wires, and coordinated
  value mutations; repair derived wires through captured constraints.
- [x] Run a planted patcher self-test so an inert oracle fails loudly.
- [x] Keep the deterministic exhaustive single-wire sweep in
  `patcher_internal`, independent of libFuzzer.

## 5. Concrete-witness validation

- [x] Treat recorded-graph rejection as inconclusive, not a soundness signal.
- [x] When patching moves a watched output while inputs remain pinned, inject
  the candidate witness into a fresh synthesis of the same circuit.
- [x] Report a soundness signal only when fresh synthesis accepts it.
- [x] Report fresh-synthesis rejection separately as capture divergence.
- [x] Fail if the seeded replay cannot rebuild and reach the selected circuit.

## Verification

```sh
cargo test -p ragu_testing
cargo test -p ragu_pcd --features unstable-fuzzing --test patcher_internal
cd qa/fuzz
cargo test --lib
cargo check --bins
```

The first two commands exercise deterministic analyzers and sweeps. The last
two compile the libFuzzer harnesses without running a campaign; scheduled fuzz
campaigns provide the guided mutation search.
