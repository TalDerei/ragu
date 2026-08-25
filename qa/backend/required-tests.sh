#!/usr/bin/env bash
# E15: the tests the lane relies on still exist under their pinned names (a
# deleted, renamed, or `#[ignore]`d test drops out of `--list` as `: test`),
# and the end-to-end harness has not grown more `prop_assume!`/`prop_filter`
# narrowing than its budget. Run after the test binaries are built; `--list`
# reuses them.
set -euo pipefail
cd "$(dirname "$0")/../.."
PIN=qa/backend/required-tests.txt
status=0
section=""
listed=""

while IFS= read -r raw; do
  line="${raw%%#*}"; line="$(echo "$line" | sed -E 's/^[[:space:]]+|[[:space:]]+$//g')"
  [ -z "$line" ] && continue
  if [[ "$line" == \[*\] ]]; then
    section="${line:1:${#line}-2}"
    if [[ "$section" == assume-budget* ]]; then
      listed=""
    else
      # shellcheck disable=SC2086
      if ! output="$(cargo test --release --locked -p $section -- --list 2>&1)"; then
        echo "$output" | tail -20
        echo "::error file=$PIN::\`cargo test -p $section -- --list\` failed to build"
        status=1; listed=""; continue
      fi
      listed="$(echo "$output" | { grep -E ': test$' || true; } | sed -E 's/: test$//')"
      [ -n "$listed" ] || { echo "::error file=$PIN::no tests listed for \`cargo test -p $section\`"; status=1; }
    fi
    continue
  fi
  if [[ "$section" == assume-budget* ]]; then
    file="${section#assume-budget }"
    count="$( { grep -cE 'prop_assume!|prop_filter' "$file" || true; } )"
    if [ "$count" -gt "$line" ]; then
      echo "::error file=$file::$count prop_assume!/prop_filter uses, budget $line; narrowing the sampled space is a review event (update $PIN deliberately)"
      status=1
    fi
    continue
  fi
  grep -qx "$line" <<< "$listed" || { echo "::error file=$PIN::required test \`$line\` is missing from \`cargo test -p $section -- --list\` (renamed, deleted, or ignored?)"; status=1; }
done < "$PIN"

[ "$status" = 0 ] && echo "required-tests.sh: ok"
exit $status
