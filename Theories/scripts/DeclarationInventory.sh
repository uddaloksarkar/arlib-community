#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Keep this source-level pattern aligned with Arlib's inventory script. It is
# stable across namespace migrations and intentionally excludes generated roots.
rg -n --with-filename \
  '^(?:noncomputable )?(?:abbrev|def|structure|class|inductive|theorem|lemma|instance)\b' \
  ArlibCommunity -g '*.lean' | sort
