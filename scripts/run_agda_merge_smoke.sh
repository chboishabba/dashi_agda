#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
agda_bin="${AGDA_BIN:-agda}"
agda_args="${AGDA_ARGS:--i . -i DCHoTT-Agda -i cubical -l standard-library}"

if [ "${1:-}" = "--list" ]; then
  exec /usr/bin/env bash "$repo_root/scripts/list_merge_agda_targets.sh" merge-smoke
fi

cd "$repo_root"

count=0
while IFS= read -r target; do
  [ -n "$target" ] || continue
  echo "=== typechecking $target ==="
  # shellcheck disable=SC2206
  agda_arg_array=($agda_args)
  "$agda_bin" "${agda_arg_array[@]}" "$target"
  count=$((count + 1))
done < <(/usr/bin/env bash "$repo_root/scripts/list_merge_agda_targets.sh" merge-smoke)

echo "typechecked $count merge-smoke targets"
