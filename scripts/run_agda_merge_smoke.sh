#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
agda_bin="${AGDA_BIN:-agda}"

if [ "${1:-}" = "--list" ]; then
  exec /usr/bin/env bash "$repo_root/scripts/list_merge_agda_targets.sh" merge-smoke
fi

cd "$repo_root"

count=0
while IFS= read -r target; do
  [ -n "$target" ] || continue
  echo "=== typechecking $target ==="
  "$agda_bin" -i . -l standard-library "$target"
  count=$((count + 1))
done < <(/usr/bin/env bash "$repo_root/scripts/list_merge_agda_targets.sh" merge-smoke)

echo "typechecked $count merge-smoke targets"
