# Optional Ragu review knowledge

These notes inform focus selection when a change can affect the properties
below. They are not mandatory passes for unrelated PRs. The general review
always runs, including for documentation, workflow, dependency and test changes.

- Circuit soundness: when constraints, gadgets, allocation, selectors, masks or
  statements change, distinguish honest host witness preparation from relations
  enforced against an adversarial prover.
- Commitment binding: follow stored values, committed polynomials, recomputed
  commitments and expected k(y) targets through both curves and their consumers.
  Rust types alone do not fix the verifier's expected setup.
- Transcripts: when message construction, ordering, encodings, domains or
  challenges can change, compare proving, native/compressed verification and
  any circuit replay.
- Recursive propagation: when accumulated claims or their checks change,
  distinguish root checks from parent circuits. Consider parents/grandparents,
  statement substitution and coordinated changes in both proof formats.
- Wallet compatibility: a claim of unchanged wallet behavior needs differential
  evidence for proof fields, compressed proofs, RNG continuation and acceptance.
  Compilation, code review or agreement within one backend does not establish it.
- Validation: distinguish production-path positive/negative controls, simulator
  tests, ignored tests, finite mutations, executed attacks and formal proofs.

Indirect changes can matter. A derive macro can alter circuit code, a feature
switch can select another verifier implementation, and a CI edit can remove the
only validation of an invariant. Investigate the concrete connection before
selecting or excluding a specialist focus. An ordinary prose correction need
not trigger a transcript or recursive-soundness review.
