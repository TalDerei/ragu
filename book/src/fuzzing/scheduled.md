# Scheduled Runs

Fuzzing finds bugs in proportion to the time it is given, so the schedule is
part of the design rather than an operational detail. This chapter will cover
how Ragu's fuzzing runs continuously and how its results are read.

## Planned contents

- **Per-pull-request checks.** Every target is built and its self-tests run on
  each pull request, without invoking libFuzzer. This catches bitrot in targets
  that would otherwise only be exercised by the scheduled runs.

- **The fuzzing cron.** Targets run matrix-parallel for hours each, several
  times a week, restoring the accumulated corpus and replaying committed
  regressions before extending it. The trade-offs behind the cadence — run
  length against corpus growth, sanitizers against throughput — belong here.

- **Coverage runs.** A separate weekly job regenerates per-target coverage from
  the accumulated corpus. The useful reading of that report is inverted: the
  uncovered lines are the map of what the search has not reached, and they
  drive the next round of target work.

## Reading a run

A scheduled run that finds nothing is the normal outcome and is not, on its
own, evidence of much. This chapter should say what does constitute evidence —
corpus growth flattening, coverage plateauing, oracle self-tests still firing —
so that a green fuzzing dashboard is interpreted honestly.
