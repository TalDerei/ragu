# CI integration

The CI formal verification workflow helps developers check whether the formal verification pipeline runs successfully.

At its core, the workflow runs the extraction exporter, builds the Lean development in `qa/lean`, and compares the circuit fingerprints computed on both sides.

Concretely, it first runs `cargo run --locked -p lean_extraction -- check`, which enforces that the checked-in generated Lean files — the `Ragu/Instances.lean` import root and the `Ragu/Fingerprint/Instances.lean` instance list — are up to date with respect to the exporter's target table.
This forces a handwritten formal-instance module to exist for every export target.

After that, CI builds the Lean project: this checks that the formal-instance files, the circuit reimplementations, and the associated proofs still compile together.
The build is run with `--wfail`, so Lean warnings (and in particular `sorry`s) are treated as failures.

> [!WARNING]
> Concretely, the Lean build step builds every module under `qa/lean/Ragu/` (the library uses a glob), so a file that no aggregator imports cannot silently escape CI.

Finally, CI runs the [fingerprint equivalence check](./fingerprint.md): it compares the canonical trace digests printed by `cargo run --locked -p lean_extraction -- fingerprint` against the ones computed in Lean from the `Clean` reimplementations (`lake env lean --run Ragu/Fingerprint/Main.lean`), and fails on any mismatch.
If the Rust circuit code changes the extracted operations or outputs, CI fails until the Lean reimplementation is updated to match (and its proofs repaired).

Independent, hand-written Lean checks should be imported through `Ragu.Contrib`, not through the Rust extraction exporter.
