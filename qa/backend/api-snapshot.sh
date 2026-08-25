#!/usr/bin/env bash
# E4: the `Backend` trait surface, minus documentation, pinned to
# qa/backend/api/ragu_backend.txt. Adding or changing a method creates a seam
# and is a frozen-tier change; this makes the surface diff explicit for review.
# Usage: qa/backend/api-snapshot.sh check|update
set -euo pipefail
cd "$(dirname "$0")/../.."
SRC=crates/ragu_backend/src/lib.rs
PIN=qa/backend/api/ragu_backend.txt

surface() {
  awk '/^pub trait Backend/ { inblk = 1 } inblk { print } inblk && /^\}/ { exit }' "$SRC" \
    | grep -vE '^\s*///' | grep -vE '^\s*$'
}

case "${1:-check}" in
  update)
    surface > "$PIN"; echo "wrote $PIN" ;;
  check)
    if grep -nE '\b(Rng|RngCore|CryptoRng|Transcript)\b' <(surface) >/dev/null; then
      echo "::error file=$SRC::Backend methods must not take randomness or a transcript"; exit 1
    fi
    if ! diff -u "$PIN" <(surface); then
      echo "::error file=$PIN::the Backend trait surface changed; a new or changed seam is a frozen-tier decision — review, then run qa/backend/api-snapshot.sh update"
      exit 1
    fi
    echo "api-snapshot.sh: ok" ;;
  *) echo "usage: $0 check|update"; exit 2 ;;
esac
