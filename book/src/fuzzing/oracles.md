# Oracles

A fuzz target is only as good as the property it checks. Ragu's targets check
five kinds.

**Completeness.** An honest witness must be accepted. A rejection means the
circuit is over-constrained — a liveness bug, found without needing to know
what the right answer was.

**Differential.** Two implementations of the same thing must agree:
`Simulator` against `Emulator<Wired<Fp>>`, the circuit sponge against the
native sponge, an assembled constraint verdict against the native evaluator.

**Metamorphic.** One implementation, two paths that must agree — a witness
re-traced after mutation, or an algebraic identity that must hold however the
circuit was built.

**Under-constraint.** Start from a satisfying witness, plant a prover-style
cheat, and demand that the constraint system rejects it. This is the family
that speaks to soundness, and the only one whose failures are exploitable.

**Robustness.** Corrupted proof bytes must not verify. This tests verifier
hardening, not soundness in the sense the protocol means.

## Two ways an oracle lies

An under-constraint oracle can fire on a cheat that no later operation ever
reads. The rejection is real and the finding is not, because the mutated wire
was irrelevant. `TRIAGE_CHEAT=1` counts the downstream reads, which separates
a dead cheat from a live one.

The opposite failure is worse, because it is silent: an oracle that *cannot*
fire looks exactly like an oracle that found no bugs, and the fuzzer reports
success either way. `PATCHER_SELFTEST=1` plants the bug the advice-patcher
oracle exists to catch and asserts that it is caught.
