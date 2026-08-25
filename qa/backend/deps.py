#!/usr/bin/env python3
"""Backend boundary censuses over cargo's dependency graph.

Subcommands (all exit non-zero with `::error::` lines on a violation):

  check      dependency direction, the sealing edge, default passthrough, and
             the pinned build-script / proc-macro sets (qa/backend/dep-census.txt)
  leakage    enabling an acceleration feature on `ragu_pcd` must not change the
             features of any package the frozen build already contains, except
             as listed in qa/backend/feature-leak-allowlist.txt
  update     regenerate the pin files from the current graph

`cargo metadata` activates every optional edge regardless of features, so it
cannot answer "what does this feature change"; `leakage` uses `cargo tree`,
which resolves like a build. `cargo metadata` is only used for the
manifest-level (`--no-deps`) checks and for the lock-level census, where a
superset is what we want to pin.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PINS = ROOT / "qa" / "backend"

FROZEN = [
    "ragu_arithmetic",
    "ragu_backend",
    "ragu_circuits",
    "ragu_core",
    "ragu_macros",
    "ragu_pasta",
    "ragu_pcd",
    "ragu_primitives",
    "ragu_testing",
]
ACCELERATION = "ragu_acceleration"
# Workspace crates `ragu_acceleration` may depend on (normal dependencies).
ACCELERATION_WORKSPACE_DEPS = {"ragu_backend", "ragu_arithmetic", "ragu_circuits"}
# The one frozen crate allowed a normal dependency on `ragu_acceleration`: the
# sealed `SelectableBackend` mapping must name the accelerated types. Flip to
# True once that dependency is optional (feature `accelerated`).
SEALING_CRATE = "ragu_pcd"
SEALING_EDGE_OPTIONAL = False
# Acceleration switches are every feature `ragu_acceleration` declares except
# these: `default` is the passthrough, `multicore` is a workspace-wide feature
# that reaches every crate by design, and `std` is empty. They are enabled
# directly on the crate (`ragu_acceleration/<feature>`), which is what
# `--all-features` and downstream builds do, not only through `ragu_pcd`'s
# forwarding features.
EXCLUDED_ACCELERATION_FEATURES = {"default", "multicore", "std"}
LEAKAGE_ROOT = "ragu_pcd"
LEAKAGE_BASES = {"default": [], "multicore": ["--features", "multicore"]}
TRIPLES = [
    "x86_64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "i686-unknown-linux-gnu",
    "thumbv7em-none-eabihf",
]

errors = 0


def error(msg, file=None):
    global errors
    errors += 1
    where = f" file={file}" if file else ""
    print(f"::error{where}::{msg}")


ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")


def cargo(*args):
    # CI exports CARGO_TERM_COLOR=always, which colours `cargo tree` output
    # even when piped; force it off and strip any escape that gets through.
    env = dict(os.environ, CARGO_TERM_COLOR="never", NO_COLOR="1")
    out = subprocess.run(
        ["cargo", *args], cwd=ROOT, check=True, capture_output=True, text=True, env=env
    ).stdout
    return ANSI.sub("", out)


def metadata(*args):
    return json.loads(cargo("metadata", "--format-version", "1", "--locked", *args))


# --- manifest-level checks --------------------------------------------------


def manifests():
    return {p["name"]: p for p in metadata("--no-deps")["packages"]}


def check_direction(pkgs):
    workspace = set(pkgs)
    acc = pkgs[ACCELERATION]
    for dep in acc["dependencies"]:
        if dep["kind"] not in (None, "build"):
            continue  # dev-dependencies may use test fixtures from anywhere
        if dep["name"] in workspace and dep["name"] not in ACCELERATION_WORKSPACE_DEPS:
            error(
                f"`{ACCELERATION}` has a {dep['kind'] or 'normal'} dependency on "
                f"workspace crate `{dep['name']}`; allowed: "
                f"{sorted(ACCELERATION_WORKSPACE_DEPS)}",
                f"crates/{ACCELERATION}/Cargo.toml",
            )
    for name in FROZEN:
        for dep in pkgs[name]["dependencies"]:
            if dep["name"] != ACCELERATION or dep["kind"] not in (None, "build"):
                continue
            if name != SEALING_CRATE:
                error(
                    f"frozen crate `{name}` depends on `{ACCELERATION}`; only "
                    f"`{SEALING_CRATE}` may (for the sealed backend selection)",
                    f"crates/{name}/Cargo.toml",
                )
            elif SEALING_EDGE_OPTIONAL and not dep["optional"]:
                error(
                    f"`{SEALING_CRATE}`'s dependency on `{ACCELERATION}` must be optional",
                    f"crates/{SEALING_CRATE}/Cargo.toml",
                )


def acceleration_features(pkgs):
    """The acceleration switches `leakage` exercises, from the crate's manifest."""
    return sorted(set(pkgs[ACCELERATION]["features"]) - EXCLUDED_ACCELERATION_FEATURES)


def check_acceleration_features(pkgs):
    """Every `ragu_pcd` feature forwarding to `ragu_acceleration` must map to
    an exercised switch (or an explicitly excluded one)."""
    exercised = set(acceleration_features(pkgs)) | EXCLUDED_ACCELERATION_FEATURES
    for feature, spec in pkgs[LEAKAGE_ROOT]["features"].items():
        for s in spec:
            if s.startswith(f"{ACCELERATION}/") or s.startswith(f"{ACCELERATION}?/"):
                target = s.split("/", 1)[1]
                if target not in exercised:
                    error(
                        f"`{LEAKAGE_ROOT}` feature `{feature}` forwards to `{s}`, which "
                        "`leakage` does not exercise; declare it in ragu_acceleration's "
                        "manifest or exclude it deliberately in qa/backend/deps.py",
                        "qa/backend/deps.py",
                    )


# --- build-graph checks (cargo tree) ---------------------------------------

TREE_LINE = re.compile(
    r"^(?P<name>\S+) v(?P<ver>\S+)(?P<extra>(?: \([^)]*\))*) \[(?P<feats>[^\]]*)\](?: \(\*\))?$"
)


def tree(root, triple=None, features=(), edges="normal,build"):
    """Map `name` -> set of enabled features for the build of `root`."""
    args = ["tree", "--locked", "-e", edges, "-p", root, "-f", "{p} [{f}]", "--prefix", "none"]
    if triple:
        args += ["--target", triple]
    if features:
        args += ["--features", ",".join(features)]
    out = {}
    for line in cargo(*args).splitlines():
        line = line.strip()
        if not line:
            continue
        m = TREE_LINE.match(line)
        if not m:
            raise SystemExit(f"unrecognised cargo tree line: {line!r}")
        feats = set(f for f in m["feats"].split(",") if f)
        # Keyed by name and version: two versions of one crate are distinct
        # packages (e.g. `hashbrown` 0.12 under `indexmap` 1 next to a newer
        # `hashbrown` in the frozen build).
        out.setdefault(f"{m['name']} v{m['ver']}", set()).update(feats)
    return out


def check_default_passthrough():
    """With default features, `ragu_pcd` must not pull any acceleration
    dependency, and `ragu_acceleration` must only depend on its allowed crates."""
    default = tree(LEAKAGE_ROOT, edges="normal")
    forbidden = sorted(n for n in default if n.startswith("zakura-halo2"))
    if forbidden:
        error(
            f"default build of `{LEAKAGE_ROOT}` pulls acceleration dependencies {forbidden}",
            f"crates/{LEAKAGE_ROOT}/Cargo.toml",
        )
    acc_direct = set(
        cargo("tree", "--locked", "-e", "normal", "-p", ACCELERATION, "--depth", "1",
              "-f", "{p}", "--prefix", "none").split()
    )
    acc_direct = {n for n in acc_direct if n.startswith("ragu_")} - {ACCELERATION}
    if acc_direct != {"ragu_arithmetic", "ragu_backend"}:
        error(
            f"default `{ACCELERATION}` workspace dependencies are {sorted(acc_direct)}, "
            "expected ragu_arithmetic and ragu_backend only",
            f"crates/{ACCELERATION}/Cargo.toml",
        )


def leakage_allowlist():
    allowed = set()
    path = PINS / "feature-leak-allowlist.txt"
    for raw in path.read_text().splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        triple, package, feature = line.split(":")
        allowed.add((triple, package, feature))
    return allowed


def check_leakage():
    allowed = leakage_allowlist()
    used = set()
    features = acceleration_features(manifests())
    print(f"acceleration switches under test: {features}")
    for triple in TRIPLES:
        for base_name, base_args in LEAKAGE_BASES.items():
            base_feats = [a for a in base_args if a != "--features"]
            base = tree(LEAKAGE_ROOT, triple, base_feats)
            for feature in features:
                with_feature = tree(LEAKAGE_ROOT, triple, base_feats + [f"{ACCELERATION}/{feature}"])
                for package in sorted(base):
                    name = package.split(" v", 1)[0]
                    if name in (LEAKAGE_ROOT, ACCELERATION):
                        continue  # their own switches are the experiment
                    added = sorted(with_feature.get(package, set()) - base[package])
                    for f in added:
                        key_any = ("*", name, f)
                        key = (triple, name, f)
                        if key_any in allowed:
                            used.add(key_any)
                        elif key in allowed:
                            used.add(key)
                        else:
                            error(
                                f"[{triple}, base={base_name}] `{feature}` enables feature "
                                f"`{f}` on `{package}`, which the frozen build already contains; "
                                f"add `{triple}:{name}:{f}` to qa/backend/feature-leak-allowlist.txt "
                                "only as a deliberate frozen-tier decision",
                                "qa/backend/feature-leak-allowlist.txt",
                            )
                new = sorted(set(with_feature) - set(base))
                if new:
                    print(f"[{triple}, base={base_name}] `{feature}` adds packages: {', '.join(new)}")
    for stale in sorted(allowed - used):
        print(f"::warning file=qa/backend/feature-leak-allowlist.txt::allowlist entry "
              f"{':'.join(stale)} no longer matches any leak; remove it")


# --- lock-level census (cargo metadata, all optional edges) ------------------


def graph():
    m = metadata("--all-features")
    pk = {p["id"]: p for p in m["packages"]}
    nodes = {n["id"]: n for n in m["resolve"]["nodes"]}
    by_name = {}
    for pid, p in pk.items():
        by_name.setdefault(p["name"], pid)

    def edges(pid):
        return [d["pkg"] for d in nodes[pid]["deps"]
                if any(k["kind"] in (None, "build") for k in d["dep_kinds"])]

    def reach(starts, skip=frozenset()):
        seen, stack = set(), list(starts)
        while stack:
            x = stack.pop()
            if x in seen or x in skip:
                continue
            seen.add(x)
            stack.extend(edges(x))
        return seen

    acc = by_name[ACCELERATION]
    frozen_reach = reach([by_name[n] for n in FROZEN], skip={acc})
    exclusive = (reach([acc]) - frozen_reach) | {acc}

    def kind(pid, k):
        return any(k in t["kind"] for t in pk[pid]["targets"])

    def names(ids, k):
        return sorted({pk[i]["name"] for i in ids if kind(i, k)})

    return {
        "frozen build-script": names(frozen_reach, "custom-build"),
        "frozen proc-macro": names(frozen_reach, "proc-macro"),
        "acceleration build-script": names(exclusive, "custom-build"),
        "acceleration proc-macro": names(exclusive, "proc-macro"),
    }


def render_census(census):
    lines = [
        "# Packages with build scripts or proc-macros, by the region of the",
        "# dependency graph that reaches them (qa/backend/deps.py). Any change is a",
        "# supply-chain decision: regenerate with `python3 qa/backend/deps.py update`",
        "# and review the diff.",
    ]
    for section, names in census.items():
        lines.append(f"[{section}]")
        lines.extend(names)
    return "\n".join(lines) + "\n"


def check_dep_census():
    path = PINS / "dep-census.txt"
    expected = render_census(graph())
    if path.read_text() != expected:
        error(
            "the set of build-script / proc-macro packages changed; run "
            "`python3 qa/backend/deps.py update` and review the diff",
            "qa/backend/dep-census.txt",
        )
        for line in difflib_lines(path.read_text(), expected):
            print(line)


def difflib_lines(a, b):
    import difflib
    return difflib.unified_diff(a.splitlines(), b.splitlines(), "pinned", "current", lineterm="")


# --- entry point ------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=["check", "leakage", "update"])
    args = parser.parse_args()

    if args.command == "update":
        (PINS / "dep-census.txt").write_text(render_census(graph()))
        print("wrote qa/backend/dep-census.txt")
        return

    if args.command == "check":
        pkgs = manifests()
        check_direction(pkgs)
        check_acceleration_features(pkgs)
        check_default_passthrough()
        check_dep_census()
    elif args.command == "leakage":
        check_leakage()

    if errors:
        print(f"{errors} boundary violation(s)")
        sys.exit(1)
    print(f"deps.py {args.command}: ok")


if __name__ == "__main__":
    main()
