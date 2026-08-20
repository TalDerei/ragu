#!/usr/bin/env python3
"""Merge per-target coverage summaries into a union view and gate regressions.

Two questions the per-target reports cannot answer on their own:

*What does fuzzing reach at all?*  A file every individual target barely
touches may still be covered between them.  A true union would merge the
`profdata` of every target and report against every instrumented binary — what
``./fuzz.sh coverage`` does locally.  In CI that means shipping tens of
megabytes of profile and hundreds of megabytes of binary between jobs, per
target, every week.  So this takes the **per-file best of** every target
instead: for each file, the highest line-coverage any single target achieved.
That is a *lower bound* on the true union (two targets covering disjoint halves
of a file report as one half, not the whole), and it is reported as one.  It is
still the right shape for the question — a file no target reaches at all shows
as zero, which is the finding that matters.

*Is coverage getting worse?*  Per-target line coverage is compared against
``coverage-baseline.json``.  A drop of more than ``--tolerance`` percentage
points fails the job.  Coverage moving down is not automatically a bug — a
corpus can be lost, a target retired, a large module added — but it should
never happen without somebody deciding it is fine and saying so by refreshing
the baseline.

The baseline is refreshed by running this with ``--update`` against a run's
summaries and committing the result.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys

# A target listed in the baseline but absent from the summaries is not a
# regression in itself — its job may have failed for an unrelated reason — but
# it is reported, because a silently missing target looks like a clean run.
MISSING = "missing"


def load_summaries(directory: pathlib.Path) -> dict[str, dict]:
    """Reads ``coverage-summary-<target>.json`` files into a dict by target."""
    out: dict[str, dict] = {}
    for path in sorted(directory.rglob("coverage-summary-*.json")):
        target = path.name.removeprefix("coverage-summary-").removesuffix(".json")
        try:
            out[target] = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            print(f"::warning::could not read {path}: {exc}", file=sys.stderr)
    return out


def percent(covered: int, total: int) -> float:
    """Line coverage as a percentage, with an empty file counting as full."""
    return 100.0 if total == 0 else 100.0 * covered / total


def target_lines(summary: dict) -> tuple[int, int]:
    """``(covered, total)`` lines across a target's whole report."""
    totals = summary["data"][0]["totals"]["lines"]
    return totals["covered"], totals["count"]


def per_file(summary: dict) -> dict[str, tuple[int, int]]:
    """``filename -> (covered, total)`` lines, for one target."""
    out = {}
    for entry in summary["data"][0]["files"]:
        lines = entry["summary"]["lines"]
        out[entry["filename"]] = (lines["covered"], lines["count"])
    return out


def union_by_file(summaries: dict[str, dict]) -> dict[str, tuple[int, int]]:
    """Per-file best-of across targets. See the module docstring."""
    best: dict[str, tuple[int, int]] = {}
    for summary in summaries.values():
        for filename, (covered, total) in per_file(summary).items():
            previous = best.get(filename)
            if previous is None or percent(covered, total) > percent(*previous):
                best[filename] = (covered, total)
    return best


def render(summaries: dict[str, dict], baseline: dict, tolerance: float) -> tuple[str, dict, bool]:
    """Builds the report, the new summary, and whether the gate failed."""
    lines: list[str] = []
    failed = False

    measured = {t: percent(*target_lines(s)) for t, s in sorted(summaries.items())}
    expected = baseline.get("targets", {})

    lines.append("## fuzz coverage union")
    lines.append("")
    if not summaries:
        lines.append("**No target summaries were produced at all.** Every coverage job")
        lines.append("either failed or found no inputs to replay.")
        return "\n".join(lines) + "\n", {"targets": {}, "files": {}}, True

    files = union_by_file(summaries)
    covered = sum(c for c, _ in files.values())
    total = sum(t for _, t in files.values())
    lines.append(
        f"Union over {len(summaries)} targets: **{percent(covered, total):.2f}%** of "
        f"{total} lines across {len(files)} workspace files."
    )
    lines.append("")
    lines.append(
        "_Per-file best-of, so this is a lower bound on the true union: two targets "
        "covering disjoint halves of a file are reported as one half._"
    )
    lines.append("")

    unreached = sorted(f for f, (c, t) in files.items() if c == 0 and t > 0)
    if unreached:
        plural = "file" if len(unreached) == 1 else "files"
        lines.append(f"### {len(unreached)} {plural} no target reaches")
        lines.append("")
        for filename in unreached[:40]:
            lines.append(f"- `{filename}`")
        if len(unreached) > 40:
            lines.append(f"- _…and {len(unreached) - 40} more_")
        lines.append("")

    lines.append("### against the baseline")
    lines.append("")
    lines.append("| target | now | baseline | delta |")
    lines.append("| --- | ---: | ---: | ---: |")
    for target in sorted(set(measured) | set(expected)):
        now = measured.get(target)
        was = expected.get(target)
        if now is None:
            lines.append(f"| `{target}` | {MISSING} | {was:.2f}% | — |")
            print(
                f"::warning::{target} is in the baseline but produced no summary; "
                "its coverage job did not report",
            )
            continue
        if was is None:
            lines.append(f"| `{target}` | {now:.2f}% | new | — |")
            continue
        delta = now - was
        flag = ""
        if delta < -tolerance:
            flag = " ⚠️"
            failed = True
            print(
                f"::error::{target} line coverage fell from {was:.2f}% to {now:.2f}% "
                f"({delta:.2f} points, tolerance {tolerance:.2f}). If this is intended, "
                "refresh qa/fuzz/coverage-baseline.json.",
            )
        lines.append(f"| `{target}` | {now:.2f}% | {was:.2f}% | {delta:+.2f}{flag} |")
    lines.append("")

    new_baseline = {
        "tolerance": tolerance,
        "targets": {t: round(p, 2) for t, p in measured.items()},
    }
    summary_json = {
        "union_line_percent": round(percent(covered, total), 2),
        "targets": new_baseline["targets"],
        "unreached_files": unreached,
    }
    return "\n".join(lines) + "\n", summary_json, failed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--summaries", required=True, type=pathlib.Path)
    parser.add_argument("--baseline", required=True, type=pathlib.Path)
    parser.add_argument("--out", type=pathlib.Path)
    parser.add_argument("--out-json", type=pathlib.Path)
    parser.add_argument(
        "--tolerance",
        type=float,
        default=None,
        help="percentage points a target may lose before the gate fails; "
        "defaults to the baseline file's own tolerance",
    )
    parser.add_argument(
        "--update",
        action="store_true",
        help="rewrite the baseline from these summaries instead of gating on it",
    )
    args = parser.parse_args()

    try:
        baseline = json.loads(args.baseline.read_text())
    except FileNotFoundError:
        baseline = {}
    tolerance = args.tolerance if args.tolerance is not None else baseline.get("tolerance", 2.0)

    summaries = load_summaries(args.summaries)
    report, summary_json, failed = render(summaries, baseline, tolerance)

    print(report)
    if args.out:
        args.out.write_text(report)
    if args.out_json:
        args.out_json.write_text(json.dumps(summary_json, indent=2, sort_keys=True) + "\n")

    if args.update:
        args.baseline.write_text(
            json.dumps(
                {"tolerance": tolerance, "targets": summary_json["targets"]},
                indent=2,
                sort_keys=True,
            )
            + "\n"
        )
        print(f"Refreshed {args.baseline}.")
        return 0

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
