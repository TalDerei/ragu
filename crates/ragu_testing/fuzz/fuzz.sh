#!/usr/bin/env bash
# Run all fuzz targets. Defaults to 5 minutes each, sequential.
#
# Usage:
#   ./fuzz.sh              # 30s each, sequential
#   ./fuzz.sh 60           # 1 min each, sequential
#   ./fuzz.sh 300 -j       # 5 min each, parallel
#   DICT=1 ./fuzz.sh       # Load dict.txt of Ragu field-element constants
#
# The DICT=1 path passes -dict=dict.txt to libFuzzer. Empirical comparison
# (60s on fuzz_element_ops): roughly flat coverage with a small features
# decrease; on fuzz_poseidon_sponge: small features and corpus increase.
# Worth trying for Poseidon-heavy targets in longer runs.
#
# Regenerate dict.txt via:
#   cargo +nightly run --release --bin extract_dict > dict.txt

set -euo pipefail
cd "$(dirname "$0")"

DURATION="${1:-30}"
PARALLEL="${2:-}"
DICT="${DICT:-}"

DICT_FLAG=""
if [[ -n "$DICT" ]]; then
  DICT_FLAG="-dict=dict.txt"
fi

TARGETS=(
  fuzz_poseidon_sponge
  fuzz_endoscalar
  fuzz_element_ops
  fuzz_revdot
  fuzz_fold_revdot
  fuzz_sxy_agreement
  fuzz_poseidon_differential
  fuzz_verify_reject
  fuzz_soundness_cheat
  fuzz_driver_metamorphic
  fuzz_witness_coverage
  fuzz_algebraic_identities
)

run_target() {
  local target="$1"
  echo "=== $target (${DURATION}s) ==="
  cargo +nightly fuzz run "$target" -- \
    $DICT_FLAG \
    -max_len=1024 \
    -max_total_time="$DURATION" \
    2>&1 | tail -5
  echo
}

if [[ "$PARALLEL" == "-j" ]]; then
  for target in "${TARGETS[@]}"; do
    run_target "$target" &
  done
  wait
else
  for target in "${TARGETS[@]}"; do
    run_target "$target"
  done
fi

echo "=== done ==="
