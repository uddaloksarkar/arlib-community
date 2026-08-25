#!/usr/bin/env bash
set -euo pipefail

community_root="$(cd "$(dirname "$0")/.." && pwd)"
core_root="$community_root/../.worktrees/arlib-hard-split"
manifest="$core_root/BOUNDARY_MANIFEST.tsv"

if ! test -f "$manifest"; then
  echo "missing core boundary manifest: $manifest" >&2
  exit 1
fi

declare -A moved_modules=()
while IFS=$'\t' read -r path owner _reason; do
  test "$path" = module && continue
  test "$owner" = community || continue
  source="$core_root/$path"
  relative="${path#Arlib/}"
  destination="$community_root/ArlibCommunity/$relative"
  mkdir -p "$(dirname "$destination")"
  if test -f "$source"; then
    cp "$source" "$destination"
  elif git -C "$core_root" cat-file -e "HEAD:$path" 2>/dev/null; then
    git -C "$core_root" show "HEAD:$path" > "$destination"
  else
    echo "missing classified source: $source" >&2
    exit 1
  fi

  old_module="${path%.lean}"
  old_module="${old_module//\//.}"
  new_module="ArlibCommunity.${old_module#Arlib.}"
  moved_modules["$old_module"]="$new_module"
done < "$manifest"

# Rewrite only import declarations here.  Declaration namespaces are migrated
# separately, after the two-package source transfer has been proven complete.
while IFS= read -r destination; do
  temporary="$(mktemp)"
  while IFS= read -r line || test -n "$line"; do
    if [[ "$line" == import\ Arlib.* ]]; then
      imported="${line#import }"
      if test -n "${moved_modules[$imported]:-}"; then
        line="import ${moved_modules[$imported]}"
      fi
    fi
    printf '%s\n' "$line" >> "$temporary"
  done < "$destination"
  mv "$temporary" "$destination"
done < <(find "$community_root/ArlibCommunity" -type f -name '*.lean' | sort)

# Produce one algorithm-facing root per former Arlib area.  Direct imports are
# intentional: the manifest, not an accidental transitive import, defines the
# public content of each community area.
for area in Algorithms Approximation Automata Communication InformationTheory \
  KnowledgeCompilation MDP MarkovChains Probability Convexity Lattice; do
  root="$community_root/ArlibCommunity/$area.lean"
  temporary="$(mktemp)"
  while IFS=$'\t' read -r path owner _reason; do
    test "$owner" = community || continue
    case "$path" in
      "Arlib/$area/"*.lean)
        old_module="${path%.lean}"
        old_module="${old_module//\//.}"
        printf 'import ArlibCommunity.%s\n' "${old_module#Arlib.}" >> "$temporary"
        ;;
    esac
  done < "$manifest"
  if test -s "$temporary"; then
    sort -u "$temporary" > "$root"
    printf '\n/-! Algorithm-facing modules extracted from `Arlib.%s`. -/\n' "$area" >> "$root"
  fi
  rm -f "$temporary"
done

echo "migrated ${#moved_modules[@]} modules into ArlibCommunity"
