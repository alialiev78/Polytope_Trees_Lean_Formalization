#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Run under `lake env`. Checking one module per process bounds memory usage.
# Challenge contains specification placeholders and is not part of Article.
checked=0
for source in Proofs/*.lean Solution.lean MainText.lean Article.lean; do
  module="${source%.lean}"
  module="${module//\//.}"
  leanchecker "$module"
  printf 'Kernel replay passed: %s\n' "$module"
  checked=$((checked + 1))
done
printf 'Kernel replay passed: %s project modules.\n' "$checked"
