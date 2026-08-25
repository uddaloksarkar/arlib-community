#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

core_root="${ARLIB_CORE_ROOT:-../.worktrees/arlib-hard-split}"
if test ! -d "$core_root/Arlib" && test -d .lake/packages/arlib/Arlib; then
  core_root=".lake/packages/arlib"
fi

baseline=80ec20e
checked=0
while IFS=$'\t' read -r snapshot expected _module disposition target; do
  test "$snapshot" = snapshot && continue
  actual=$(git show "$baseline:$snapshot" | sha256sum)
  actual="${actual%% *}"
  if test "$actual" != "$expected"; then
    echo "error: provenance hash mismatch for $snapshot" >&2
    exit 1
  fi
  case "$disposition" in
    migrated-community)
      test -f "$target" || {
        echo "error: migrated target is missing: $target" >&2
        exit 1
      }
      ;;
    retained-core)
      test -f "$core_root/$target" || {
        echo "error: retained core target is missing: $target" >&2
        exit 1
      }
      ;;
    snapshot-only)
      test "$target" = - || {
        echo "error: snapshot-only row has an active target: $snapshot" >&2
        exit 1
      }
      ;;
    *)
      echo "error: invalid snapshot disposition: $disposition" >&2
      exit 1
      ;;
  esac
  checked=$((checked + 1))
done < SNAPSHOT_PROVENANCE.tsv

test "$checked" -eq 485 || {
  echo "error: expected 485 snapshot rows, checked $checked" >&2
  exit 1
}

echo "snapshot provenance audit passed ($checked files)"
