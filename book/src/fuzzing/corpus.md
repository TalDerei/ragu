# Corpus and Triage

A coverage-guided fuzzer is only as strong as the corpus it starts from, and a
crash is only useful once it has been reduced to a cause. This chapter will
cover both halves of that operational story.

## Planned contents

- **Corpus accumulation.** Each target keeps its own corpus, restored at the
  start of a scheduled run and saved at the end — including runs that ended in
  a crash. Minimization keeps the corpus from growing without adding coverage.

- **The constant dictionary.** Ragu's field-element constants — the Poseidon
  round constants and MDS matrices for both fields, plus special values such as
  the cube root of unity — are extracted into a libFuzzer dictionary. It ships
  opt-in rather than always-on, because it helps on sponge-heavy targets and is
  roughly neutral elsewhere; the reasoning behind that default belongs here.

- **Committed regressions.** Every crash that has been fixed leaves a committed
  input that is replayed on each run, so a fix cannot silently regress.

- **Triage.** Reducing an artifact to a readable cause: printing the decoded
  input rather than raw bytes, and — for the under-constraint targets —
  measuring whether a cheated wire was ever read downstream, which separates a
  real finding from a dead cheat.

## What a finding looks like

The chapter should close with a worked example: a real crash artifact, the
commands that turned it into a diagnosis, and the fix. Several of the bugs
already found are good candidates, including a precondition violation on
squeezing from an empty sponge, an asymmetry between the native and circuit
sponge APIs, and a divide-by-zero reachable through registry key construction.
