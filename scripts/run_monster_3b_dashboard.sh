#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${1:-$ROOT/artifacts/monster-3b}"
JSON="$OUT/mn3b-restriction.json"

mkdir -p "$OUT"

if ! command -v gap >/dev/null 2>&1; then
  echo "error: GAP is required" >&2
  exit 1
fi

python_bin="${PYTHON:-python3}"
if ! command -v "$python_bin" >/dev/null 2>&1; then
  echo "error: Python 3 is required" >&2
  exit 1
fi

# The GAP script itself loads CTblLib and fails closed when the current
# library lacks M, MN3B, or the stored MN3B -> M fusion.
gap -q "$ROOT/scripts/gap/monster_3b_normalizer_restriction.g" > "$JSON"

"$python_bin" "$ROOT/scripts/visualize_monster_3b_normalizer.py" \
  --restriction-json "$JSON" \
  --output "$OUT"

printf 'Monster 3B dashboard written to %s\n' "$OUT"
