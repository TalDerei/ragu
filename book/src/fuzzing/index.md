# Overview

Formal verification proves things about the circuits it covers, and the
[previous part](../fv/index.md) is explicit about how narrow that coverage is
today. Fuzzing covers the rest, and it covers it differently: instead of a
proof about one gadget, a coverage-guided search over millions of generated
programs, looking for the input that breaks an invariant nobody thought to
test.

The two techniques answer different questions. A proof says a property holds
for every input. A fuzzer says it failed to find a counterexample in the region
it explored — weaker, but available for parts of the system no proof reaches
yet, including the recursion circuits, the staging system, and the full witness
pipeline.

## The harness

Ragu's fuzzing lives in `qa/fuzz`, a standalone cargo-fuzz workspace holding 24
targets plus a dictionary-extraction tool. It is its own workspace root so that
the nightly toolchain and libFuzzer flags it needs do not leak into the rest of
the repository.

Most targets share one substrate: a byte decoder that turns the fuzzer's raw
input into a program over a stack of gadget calls, with a common op grammar and
driver-generic synthesis. Targets carve their vocabulary out of that union, so
corpora are shared and a mutation that reaches deep circuit structure in one
target reaches it in the others.

## Oracles, not crashes

The interesting question for a proof system is not whether the code panics. It
is whether a witness that should be rejected is accepted. Ragu's targets are
built around explicit [oracles](oracles.md) — a property checked on every
input, whose violation is the finding.

The oracles fall into a few families: completeness (an honest witness must be
accepted), differential and metamorphic (two implementations, or two paths
through one implementation, must agree), under-constraint (a planted cheat must
be rejected), and robustness (a corrupted proof must not verify). The
under-constraint family is the one that speaks to soundness, and it is the
hardest to get right — an oracle that never fires on a real bug is worse than
no oracle, so several targets ship a planted-bug self-test that proves the
oracle can fire.

## What remains to be written

- [Oracles](oracles.md) — the property each family checks, why it is the right
  property, and how a planted-bug self-test establishes that the oracle has
  teeth.
- [Targets](targets.md) — the catalog: what each target generates, what it
  asserts, and which bugs it has caught.
- [Corpus and triage](corpus.md) — corpus accumulation, the field-constant
  dictionary, committed crash regressions, and the environment variables for
  reducing a crash artifact to a readable cause.
- [Scheduled runs](scheduled.md) — the cron and coverage workflows, and how to
  read a coverage report as a map of what the search has not reached.
