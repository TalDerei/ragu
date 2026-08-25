#!/usr/bin/env bash
# Source-level backend boundary censuses. Each check prints a `::error::` line
# and the script exits non-zero if any check fails. See qa/backend/README.md.
set -euo pipefail
cd "$(dirname "$0")/../.."

ACC=crates/ragu_acceleration
LIB=$ACC/src/lib.rs
VERIFY=crates/ragu_pcd/src/verify.rs
VERIFIER_KERNELS='sparse_eval|sparse_revdot|registry_circuit_y|registry_wxy'
status=0
fail() { echo "::error file=$1::$2"; status=1; }

# Extract the body of `impl ragu_backend::Backend for <type>` from lib.rs
# (rustfmt puts the closing brace in column 0).
impl_block() {
  awk -v ty="$1" '
    $0 ~ "^impl ragu_backend::Backend for " ty " \\{" { inblk = 1; next }
    inblk && /^\}/ { inblk = 0 }
    inblk { print }
  ' "$LIB"
}
override_names() { impl_block "$1" | { grep -E '^    fn [a-z_]+' || true; } | sed -E 's/^    fn ([a-z_]+).*/\1/'; }
# Body of one override inside an impl block: from its `fn` line up to the next.
override_body() {
  impl_block "$1" | awk -v name="$2" '
    $0 ~ "^    fn " name "[^a-z_]" { inf = 1; print; next }
    inf && /^    fn / { inf = 0 }
    inf { print }
  '
}

# The censuses below parse the two impl blocks; if either header is not found
# on one line (rustfmt keeps `impl Trait for Type {` on one line at these
# lengths) every per-override check would pass vacuously, so fail loudly.
for ty in AcceleratedBackend AcceleratedProver; do
  grep -qE "^impl ragu_backend::Backend for $ty \{" "$LIB" \
    || fail "$LIB" "could not find \`impl ragu_backend::Backend for $ty {\` on one line; the census parses that header"
done
[ -n "$(override_names AcceleratedBackend)" ] \
  || fail "$LIB" "no overrides found in \`impl ragu_backend::Backend for AcceleratedBackend\`; the census expects at least one (msm)"

# --- E7: every override is feature-gated with a reference fallback ----------
for name in $(override_names AcceleratedBackend); do
  body=$(override_body AcceleratedBackend "$name")
  grep -q '#\[cfg(feature = "' <<< "$body" || fail "$LIB" "override \`$name\` has no \`#[cfg(feature = ...)]\` arm"
  grep -q '#\[cfg(not(feature = "' <<< "$body" || fail "$LIB" "override \`$name\` has no \`#[cfg(not(feature = ...))]\` reference fallback"
  if grep -E 'cfg\(' <<< "$body" | grep -vE 'cfg\((not\()?feature = "' >/dev/null; then
    fail "$LIB" "override \`$name\` uses a \`cfg\` other than \`feature = ...\`; the code CI runs must be the code users run"
  fi
done

# --- E7: AcceleratedProver forwards exactly the same overrides ---------------
if [ "$(override_names AcceleratedBackend)" != "$(override_names AcceleratedProver)" ]; then
  fail "$LIB" "AcceleratedBackend and AcceleratedProver override different methods: [$(override_names AcceleratedBackend | tr '\n' ' ')] vs [$(override_names AcceleratedProver | tr '\n' ' ')]"
fi

# --- E2: every override ships transition sizes and a test consumes them -----
for name in $(override_names AcceleratedBackend); do
  f=qa/backend/transitions/$name.txt
  [ -s "$f" ] || fail "$f" "override \`$name\` has no transition-size list (algorithm boundaries the proptest strategy cannot generate)"
  grep -rlq "transitions/$name.txt" "$ACC/tests" || fail "$f" "no test under $ACC/tests includes \`transitions/$name.txt\`"
done

# --- E11: every override has a benchmark pair for the perf gate --------------
BENCH=crates/ragu_pcd/benches/gungraun.rs
for name in $(override_names AcceleratedBackend); do
  pair=$({ grep -E "^$name: " qa/backend/bench-pairs.txt || true; } | head -1 | sed -E "s/^$name: //")
  [ -n "$pair" ] || { fail "qa/backend/bench-pairs.txt" "override \`$name\` has no benchmark pair (reference and accelerated end-to-end benchmarks)"; continue; }
  for bench in $pair; do
    grep -qE "^fn $bench\(" "$BENCH" || fail "$BENCH" "benchmark \`$bench\` named in qa/backend/bench-pairs.txt for \`$name\` does not exist"
  done
done

# --- E16: verifier-consulted kernels are confined to src/verifier/ ---------
for name in $(override_names AcceleratedBackend | grep -E "^($VERIFIER_KERNELS)$" || true); do
  override_body AcceleratedBackend "$name" | grep -q 'verifier::' \
    || fail "$LIB" "verifier-consulted override \`$name\` must delegate to \`verifier::\` (src/verifier/)"
done
if grep -nE '\bB::' "$VERIFY" >/dev/null; then
  fail "$VERIFY" "verify.rs calls the selected backend directly; use \`Verifier::<B>::\` so acceptance kernels follow the sealed Verifier selection"
fi
# Every backend method the verifier can reach — directly in verify.rs, or
# through `claims::Builder` (internal/claims.rs), which verify.rs instantiates
# with the Verifier type — must be in the documented verifier-consulted set.
CLAIMS=crates/ragu_pcd/src/internal/claims.rs
for name in $({ grep -oE 'Verifier::<B>::[a-z_]+' "$VERIFY" || true; } | sed 's/.*:://' | sort -u); do
  grep -qE "^($VERIFIER_KERNELS)$" <<< "$name" \
    || fail "$VERIFY" "verify.rs uses backend method \`$name\`, which is not in the documented verifier-consulted set ($VERIFIER_KERNELS); update ragu_backend's docs, this script, and src/verifier/"
done
for name in $({ grep -oE '\bB::[a-z_]+' "$CLAIMS" || true; } | sed 's/.*:://' | sort -u); do
  grep -qE "^($VERIFIER_KERNELS)$" <<< "$name" \
    || fail "$CLAIMS" "claims::Builder uses backend method \`$name\`; the verifier reaches Builder, so it joins the verifier-consulted set ($VERIFIER_KERNELS): update ragu_backend's docs, this script, and src/verifier/"
done
# Verifier kernels must not branch on field or point values (best effort:
# comparisons and matches inside src/verifier/).
if ls "$ACC"/src/verifier/*.rs >/dev/null 2>&1; then
  if grep -nE '^\s*(if|match|while)\b' "$ACC"/src/verifier/*.rs | grep -vE '\.(len|is_empty|chunks|windows|iter)\(' >/dev/null; then
    fail "$ACC/src/verifier" "control flow in src/verifier/ must not depend on field or point values; shape-dependent loops only"
  fi
fi

# --- E9: unsafe budget, SAFETY comments, build scripts, lints ----------------
pinned=$(tr -d '[:space:]' < qa/backend/unsafe-census.txt)
count=0
while IFS= read -r file; do
  n=$(sed -E 's://.*$::' "$file" | { grep -ow 'unsafe' || true; } | wc -l | tr -d ' ')
  count=$((count + n))
  while IFS=: read -r line _; do
    start=$((line > 3 ? line - 3 : 1))
    sed -n "${start},${line}p" "$file" | grep -q 'SAFETY:' \
      || fail "$file" "\`unsafe\` at line $line has no \`// SAFETY:\` comment within the three preceding lines"
  done < <(sed -E 's://.*$::' "$file" | grep -nw 'unsafe' || true)
done < <(find "$ACC/src" -name '*.rs')
[ "$count" = "$pinned" ] || fail "qa/backend/unsafe-census.txt" "\`unsafe\` occurrences in $ACC/src: $count, pinned: $pinned (update the pin deliberately)"
[ ! -e "$ACC/build.rs" ] || fail "$ACC/build.rs" "ragu_acceleration must not have a build script"
grep -q '#!\[deny(missing_docs)\]' "$LIB" || fail "$LIB" "missing \`#![deny(missing_docs)]\`"
grep -q '#!\[deny(unsafe_op_in_unsafe_fn)\]' "$LIB" || fail "$LIB" "missing \`#![deny(unsafe_op_in_unsafe_fn)]\`"
[ ! -e .gitmodules ] || fail ".gitmodules" "git submodules are not allowed"

# --- E9: determinism — no ambient entropy or time in the acceleration crate --
if grep -rnE 'rand::|getrandom|thread_rng|OsRng|SystemTime|Instant::now|std::time|thread::current' "$ACC/src" >/dev/null; then
  grep -rnE 'rand::|getrandom|thread_rng|OsRng|SystemTime|Instant::now|std::time|thread::current' "$ACC/src"
  fail "$LIB" "acceleration code must be deterministic in its arguments: no randomness, time, or thread identity"
fi

# --- E9: no unreviewed cross-tier source inclusion ----------------------------
# The backend-equivalence test sources live in their canonical `tests/`
# folder, but compile as crate-internal modules so they can inspect private
# proof state. Those two exact paths are the only allowed indirection.
path_uses="$({ grep -rn '#\[path' crates/*/src || true; })"
unexpected_paths="$({ grep -vE '^(crates/ragu_pcd/src/lib.rs:[0-9]+:#\[path = "\.\./tests/backend_equivalence/mod.rs"\]|crates/ragu_pcd/src/proof/mod.rs:[0-9]+:#\[path = "\.\./\.\./tests/backend_equivalence/proof.rs"\])$' <<< "$path_uses" || true; })"
if [ -n "$unexpected_paths" ]; then
  echo "$unexpected_paths"
  fail "crates" "only the canonical ragu_pcd backend-equivalence test modules may use \`#[path]\`"
fi
if grep -rnE 'include(_str|_bytes)?!\(' crates/*/src | grep -E '\.\./|ragu_acceleration' >/dev/null; then
  grep -rnE 'include(_str|_bytes)?!\(' crates/*/src | grep -E '\.\./|ragu_acceleration'
  fail "crates" "\`include!\` must not reach outside its crate"
fi

# --- E5: only the sealing file names ragu_acceleration in frozen crate sources
for name in ragu_arithmetic ragu_backend ragu_circuits ragu_core ragu_macros ragu_pasta ragu_pcd ragu_primitives ragu_testing; do
  while IFS= read -r file; do
    case "$file" in
      crates/ragu_pcd/src/backend.rs) continue ;;
    esac
    fail "$file" "frozen crate source names \`ragu_acceleration\`; only crates/ragu_pcd/src/backend.rs (the sealed selection) may"
  done < <(grep -rlE 'ragu_acceleration::|use ragu_acceleration|extern crate ragu_acceleration' "crates/$name/src" 2>/dev/null || true)
done

[ "$status" = 0 ] && echo "census.sh: ok"
exit $status
