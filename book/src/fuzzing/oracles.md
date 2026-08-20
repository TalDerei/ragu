# Oracles

A fuzz target is only as good as the property it checks. This chapter will
cover the oracle families Ragu's targets are built from, and what each one can
and cannot establish.

## Planned contents

- **Completeness oracles.** An honest witness through an anchorless,
  value-infallible circuit must be accepted. Rejection is an over-constraint
  signal, independent of any repair search.

- **Differential oracles.** The same generated program run through two
  implementations must agree — `Simulator` against `Emulator<Wired<_>>`, the
  circuit sponge against the native sponge, an assembled constraint verdict
  against a native shadow computation.

- **Metamorphic oracles.** One implementation, two paths that must agree: a
  witness re-traced after mutation, a polynomial evaluated in two bases, a
  registry consistency identity that must hold however the circuit was built.

- **Under-constraint oracles.** The soundness-relevant family. Start from a
  satisfying witness, introduce a prover-style cheat, and demand rejection.
  The distinctions that matter here — mutating a witness input and re-tracing
  versus repairing through the captured constraint graph, and why the latter
  catches under-constrained advice that the former masks — deserve their own
  treatment.

- **Robustness oracles.** Corrupt proof bytes must be rejected by the verifier.
  This tests hardening of the implementation, not soundness in the sense the
  protocol means.

## Why oracle self-tests matter

An oracle that cannot fire is indistinguishable from an oracle that finds no
bugs, and the fuzzer will report success either way. Several targets carry a
planted-bug mode that deliberately introduces the flaw the oracle exists to
catch and asserts that it is caught. This chapter should explain the failure
modes that motivate those self-tests, including dead cheats — a cheated wire
that no downstream operation ever reads, which produces a signal that looks
like a soundness finding and is not.
