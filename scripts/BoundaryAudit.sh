#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if rg -n '^import ArlibCommunity(?:\.|$)' .worktrees/arlib-hard-split/Arlib \
    .worktrees/arlib-hard-split/Arlib.lean; then
  echo 'error: core Arlib imports ArlibCommunity' >&2
  exit 1
fi

if rg -n '^namespace Arlib(?:\.|$)' ArlibCommunity; then
  echo 'error: community source still declares in the Arlib namespace' >&2
  exit 1
fi

echo 'ArlibCommunity boundary audit passed'

