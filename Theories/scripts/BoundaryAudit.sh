#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

core_root="${ARLIB_CORE_ROOT:-../.worktrees/arlib-hard-split}"

if test ! -d "$core_root/Arlib" && test -d .lake/packages/arlib/Arlib; then
  core_root=".lake/packages/arlib"
fi

if test ! -d "$core_root/Arlib"; then
  echo "error: Arlib core not found at $core_root (set ARLIB_CORE_ROOT)" >&2
  exit 1
fi

if rg -n '^import ArlibCommunity(?:\.|$)' "$core_root/Arlib" \
    "$core_root/Arlib.lean"; then
  echo 'error: core Arlib imports ArlibCommunity' >&2
  exit 1
fi

if rg -n '^namespace Arlib(?:\.|$)' ArlibCommunity; then
  echo 'error: community source still declares in the Arlib namespace' >&2
  exit 1
fi

if rg -n '^namespace ArlibCommunity(?:\.|$)' "$core_root/Arlib" \
    "$core_root/Arlib.lean"; then
  echo 'error: core source declares in the ArlibCommunity namespace' >&2
  exit 1
fi

legacy_sources=()
while IFS= read -r source_dir; do
  legacy_sources+=("$source_dir")
done < <(find . -mindepth 2 -type d -name src -not -path './.lake/*' -print)
if test "${#legacy_sources[@]}" -ne 0; then
  printf 'error: legacy snapshot source tree remains: %s\n' \
    "${legacy_sources[@]}" >&2
  exit 1
fi

if rg --files-without-match '^namespace ArlibCommunity\.MarkovChains\.Continuous(?:\.|$)' \
    ArlibCommunity/MarkovChains/Continuous/*.lean; then
  echo 'error: a community continuous-chain module uses the legacy namespace' >&2
  exit 1
fi

if rg --files-without-match '^namespace Arlib\.MarkovChains\.Continuous(?:\.|$)' \
    "$core_root"/Arlib/MarkovChains/Continuous/*.lean; then
  echo 'error: a core continuous-chain module uses the legacy namespace' >&2
  exit 1
fi

if test "$(awk -F '\t' 'NR > 1 { count++ } END { print count + 0 }' \
    SNAPSHOT_PROVENANCE.tsv)" -ne 485; then
  echo 'error: snapshot provenance ledger does not contain 485 entries' >&2
  exit 1
fi

baseline_count=$(wc -l < "$core_root/DECLARATION_INVENTORY.baseline.txt")
core_count=$("$core_root/scripts/DeclarationInventory.sh" | wc -l)
community_count=$(scripts/DeclarationInventory.sh | wc -l)
if test "$((core_count + community_count))" -lt "$baseline_count"; then
  printf 'error: declaration inventory shrank: baseline=%d union=%d\n' \
    "$baseline_count" "$((core_count + community_count))" >&2
  exit 1
fi

printf 'ArlibCommunity boundary audit passed (declarations: %d baseline, %d union)\n' \
  "$baseline_count" "$((core_count + community_count))"
