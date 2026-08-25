#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

while IFS= read -r source_file; do
  temporary="$(mktemp)"
  while IFS= read -r line || test -n "$line"; do
    if [[ "$line" =~ ^namespace\ (Arlib)(\..*)?$ ]]; then
      old_namespace="${BASH_REMATCH[1]}${BASH_REMATCH[2]:-}"
      suffix="${old_namespace#Arlib}"
      printf 'namespace ArlibCommunity%s\n' "$suffix" >> "$temporary"
    elif [[ "$line" =~ ^end\ Arlib(\..*)?$ ]]; then
      printf 'end ArlibCommunity%s\n' "${BASH_REMATCH[1]:-}" >> "$temporary"
    else
      printf '%s\n' "$line" >> "$temporary"
    fi
  done < "$source_file"
  mv "$temporary" "$source_file"
done < <(find ArlibCommunity -type f -name '*.lean' ! -path 'ArlibCommunity/Init.lean' | sort)

# These namespaces are wholly community-owned after extraction, so qualified
# references to them must cross the new package boundary as well.
while IFS= read -r source_file; do
  sed -i \
    -e 's/Arlib\.Algorithms/ArlibCommunity.Algorithms/g' \
    -e 's/Arlib\.Approximation\.LewisWeights/ArlibCommunity.Approximation.LewisWeights/g' \
    -e 's/Arlib\.KnowledgeCompilation\.BranchingPrograms/ArlibCommunity.KnowledgeCompilation.BranchingPrograms/g' \
    -e 's/Arlib\.KnowledgeCompilation\.Forgetting/ArlibCommunity.KnowledgeCompilation.Forgetting/g' \
    -e 's/Arlib\.KnowledgeCompilation\.LowerBounds/ArlibCommunity.KnowledgeCompilation.LowerBounds/g' \
    -e 's/Arlib\.KnowledgeCompilation\.Tseitin/ArlibCommunity.KnowledgeCompilation.Tseitin/g' \
    -e 's/Arlib\.MarkovChains\.Chains/ArlibCommunity.MarkovChains.Chains/g' \
    -e 's/Arlib\.Lattice\.Rounding/ArlibCommunity.Lattice.Rounding/g' \
    -e 's/Arlib\.GaussianCooling/ArlibCommunity.GaussianCooling/g' \
    -e 's/Arlib\.PointwiseRoute/ArlibCommunity.PointwiseRoute/g' \
    -e 's/Arlib\.Probability\.StochApprox/ArlibCommunity.Probability.StochApprox/g' \
    "$source_file"
done < <(find ArlibCommunity -type f -name '*.lean' | sort)

echo 'hardened ArlibCommunity declaration namespaces'
