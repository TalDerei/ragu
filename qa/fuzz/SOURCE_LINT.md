# Ragu circuit source lint

`circuit_lint` is the no-execution front end of Ragu's under-constraint
analysis pipeline. It lives entirely in the standalone `qa/fuzz` workspace and
parses production Rust source with `syn`; the analysis does not typecheck or
execute the inspected code, synthesize constraints, or invoke witness closures.

The current rules are intentionally narrow:

- `RAGU001` (error): a fallible driver or gadget result is discarded without
  `?`, matching, or explicit handling, including through underscore bindings
  or `drop`/`forget` wrappers.
- `RAGU002` (error): a witness-assignment closure mutates captured state.
- `RAGU003` (error): witness-observable state controls code that emits driver
  or gadget operations, including match guards, short-circuit expressions,
  `let-else`, and branches that exit before later operations.
- `RAGU004` (advisory): a driver-produced constraint value is explicitly
  discarded, including part of a destructuring pattern.
- `RAGU005` (advisory): conditional arms emit different syntactic operation
  shapes.
- `RAGU006` (error): a reviewed QA-baseline entry no longer matches its exact
  rule, source path, and line.

Run the same strict gate as CI:

```sh
cd qa/fuzz
./fuzz.sh source-lint
```

Error-level findings cannot be suppressed. Reviewed advisory exceptions live
in `qa/fuzz/source-lint-baseline.txt`, keyed by exact rule, repository-relative
path, and source line with a rationale. A source edit that moves or removes a
finding makes its baseline entry stale and fails the gate. Production files do
not carry linter annotations.

The existing fuzz-harness CI job runs this scan through the QA library test;
the binary is the focused local entry point. Both implementations use the same
analyzer and baseline.

This AST pass is not a proof that every intended constraint exists. Rust syntax
does not encode the circuit specification, and `syn` does not provide resolved
types or MIR def-use chains. Constraint-emission rules currently require a
direct `&mut D` parameter, while associated witness constructors such as
`D::just` are also checked in driver-generic helpers without one. Helpers that
store or alias a driver require the type-aware follow-up, and macro bodies are
not expanded. Post-synthesis connectivity/rank checks and patcher fuzzing remain
necessary; expanded, type-aware HIR/MIR taint analysis is not implemented yet.
