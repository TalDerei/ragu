#!/usr/bin/env bash
# Check that every Ragu FV endpoint has a direct trust-boundary pin.
#
# Ported and adapted from zcash/ironwood's scripts/check_endpoint_census.sh at commit
# 3c056cbebf2880b54f801c348cb67ce7dc9f2a05. Ragu's marker-anywhere policy intentionally closes
# that snapshot's qualified _prob_le_of_... endpoint-discovery escape.
#
# This source-tree pass sees a newly added module even before it enters `Ragu.Meta.TrustBoundary`'s
# import closure. `Ragu.Meta.CensusCheck` performs the complementary elaborated-environment check,
# which
# sees every declaration kind and syntax form in that closure. The marker rule deliberately allows
# qualifiers after `soundness` / `completeness`; naming an endpoint `_of_...` or `_at_...` must not
# remove its trust obligation.
set -euo pipefail
cd "$(dirname "$0")/.."

ENDPOINT_RE='(^|_)(soundness|completeness|error_bound|finite_security|measure_le|probability_bound|prob_le|capstone)([^A-Za-z0-9]|$)|^(p_prime|q_prime|fingerprint|instances)$'

source_root='qa/fv/Ragu'
census='qa/fv/Ragu/Meta/TrustBoundary.lean'

if [[ ! -f "$census" ]]; then
  echo "VIOLATION: no Ragu FV trust-boundary census found" >&2
  exit 1
fi

sources=$(find "$source_root" -name '*.lean' \
  -not -path "$source_root/Meta/Tests/*" \
  -not -path "$source_root/Meta/TrustBoundary.lean" \
  -not -path "$source_root/Meta/CensusCheck.lean" | sort)

pins=$(grep -hE '^census_(axioms|computable) ' "$census" \
  | sed -E 's/^census_(axioms|computable)[[:space:]]+//; s/^_root_\.//; s/[[:space:]].*$//' \
  | sort -u || true)

status=0
count=0
circuit_count=0

# Every circuit module is imported directly into the trust boundary. This closes the source
# parser's syntax gap: once a module is in the elaborated closure, a custom command or multiline
# declaration cannot hide an endpoint from `assert_endpoint_census`.
circuit_sources=$(find "$source_root/Circuits" -name '*.lean' | sort)
while IFS= read -r file; do
  module=${file#qa/fv/}
  module=${module%.lean}
  module=${module//\//.}
  circuit_count=$((circuit_count + 1))
  if ! grep -qxF "import $module" "$census"; then
    echo "VIOLATION: circuit module ${module} (${file}) is absent from the trust-boundary import closure" >&2
    status=1
  fi
done <<< "$circuit_sources"

while IFS= read -r file; do
  namespace_path=''
  while IFS= read -r line || [[ -n "$line" ]]; do
    if [[ $line =~ ^namespace[[:space:]]+([A-Za-z0-9_.\']+) ]]; then
      opened=${BASH_REMATCH[1]}
      if [[ -z $namespace_path ]]; then
        namespace_path=$opened
      else
        namespace_path="${namespace_path}.${opened}"
      fi
      continue
    fi

    if [[ $line =~ ^end[[:space:]]+([A-Za-z0-9_.\']+) ]]; then
      closed=${BASH_REMATCH[1]}
      if [[ $namespace_path == "$closed" ]]; then
        namespace_path=''
      elif [[ $namespace_path == *."$closed" ]]; then
        namespace_path=${namespace_path%."$closed"}
      fi
      continue
    fi

    if [[ $line =~ ^private[[:space:]] ]]; then continue; fi
    [[ $line =~ ^((protected|noncomputable|partial|unsafe)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|axiom|opaque|inductive|structure|class)[[:space:]]+([A-Za-z0-9_.\']+) ]] || continue

    declared=${BASH_REMATCH[4]}
    if [[ $declared == *.* || -z $namespace_path ]]; then
      qualified=$declared
    else
      qualified="${namespace_path}.${declared}"
    fi

    base=${declared##*.}
    # `main` is exact: a generic namespace-local `main` is not the fingerprint executable boundary.
    [[ $base =~ $ENDPOINT_RE || $qualified == main ]] || continue

    count=$((count + 1))
    if ! grep -qxF "$qualified" <<< "$pins"; then
      echo "VIOLATION: endpoint ${qualified} (${file}) has no direct census_axioms/census_computable entry" >&2
      status=1
    fi
  done < "$file"
done <<< "$sources"

if [[ $status -eq 0 ]]; then
  echo "Ragu FV endpoint census: ${circuit_count} circuit module(s) imported; ${count} endpoint declaration(s), all directly pinned."
fi
exit $status
