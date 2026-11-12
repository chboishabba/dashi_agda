#!/usr/bin/env bash
set -euo pipefail

# Native Agda 2.9 / Nix source-kernel regression; never substitutes CI.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Analysis/ZetaOddValueWitnessTransportExact.agda
  DASHI/Analysis/ZetaZ7AgdaIndexTransportExact.agda
  DASHI/Analysis/RiemannOddIrrationalityClayBoundaryExact.agda
)

for source in "${targets[@]}"; do
  test -s "$source" || { echo "missing source $source" >&2; exit 1; }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--type-in-type|TERMINATING|NON_COVERING' "$source"; then
    echo "forbidden trust escape in $source" >&2
    exit 1
  fi
  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "unsolved Agda hole in $source" >&2
    exit 1
  fi
done

# This is the existing Nix-pinned, shadow-worktree local Agda runner.
# It may need AGDA_FLAKE/AGDA_STDLIB_SRC_29 set by the user's environment.
bash scripts/run_agda29_parallel_check.sh "${targets[@]}"
echo "Focused Bishop/Z7/RH-boundary Agda 2.9 regression completed."
