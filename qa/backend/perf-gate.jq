# Perf gate for the accelerated backend (qa/backend/README.md).
#
# Input: array of gungraun summary objects (`--slurp` over every
# `target/gungraun/**/summary.json`). Args: --argjson tolerance <ratio>
# (accelerated Ir may be at most `tolerance` × reference Ir; 1.0 = must not
# cost more). Output: one verdict object per pair from
# qa/backend/bench-pairs.txt; with `--exit-status` a failing verdict exits 1.
#
# Only the Ir (instruction count) metric is compared; it is deterministic
# under valgrind and unaffected by `--cache-sim=no`. Regression against the
# base branch is gungraun's own `--callgrind-limits` check, not this file.

def ir:
  .profiles[0].summaries.total.summary.Callgrind.Ir.metrics
  | (if .Both then .Both[0] elif .Left then .Left else null end)
  | (if . == null then null elif .Int then .Int elif .Float then .Float else null end);

def find(name):
  [.[] | select(.function_name == name)] | first // null;

[
  {
    method: "msm",
    reference: (find("fuse") | if . == null then null else ir end),
    accelerated: (find("fuse_accelerated") | if . == null then null else ir end)
  }
]
| map(
    . + {
      ok: (.reference != null and .accelerated != null and .accelerated <= .reference * $tolerance),
      ratio: (if .reference != null and .accelerated != null and .reference > 0
              then (.accelerated / .reference) else null end)
    })
| (.[] | "\(.method): accelerated Ir \(.accelerated // "missing") vs reference Ir \(.reference // "missing") (ratio \(.ratio // "n/a"), tolerance \($tolerance)) -> \(if .ok then "ok" else "FAIL" end)")
, (all(.[]; .ok))
