# Scheduled Runs

Fuzzing finds bugs in proportion to the time it is given, so the schedule is
part of the design. Three workflows carry it.

**Per pull request.** `rust.yml` builds every target and runs the substrate,
recorder, and planted-bug self-tests, without invoking libFuzzer. This is what
catches bitrot in a target that no one has run in months.

**Three times a week.** `fuzz-cron.yml` runs every target matrix-parallel for
five hours each, on Sundays, Wednesdays, and Fridays at 00:00 UTC. Each job
restores its corpus, replays the committed regressions, extends the corpus,
and saves it whether or not it crashed. Crash artifacts are kept for 30 days;
a manual run can override the duration and load the dictionary.

**Mondays.** `fuzz-coverage.yml` runs at 06:00 UTC, after the Sunday fuzz run,
and regenerates per-target `llvm-cov` reports from the accumulated corpora and
any committed seeds. Read them backwards: the uncovered lines are the map of
what the search has not reached, and that map is what drives the next round of
target work.

A green run means the search found nothing this week, which is the normal
outcome and evidence of very little on its own. Corpus growth flattening and
coverage plateauing are what indicate a target has been exhausted.
