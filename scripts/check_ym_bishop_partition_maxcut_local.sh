#!/usr/bin/env bash
set -euo pipefail

# Native Nix/Agda 2.9 verification. No Docker or CI requirement.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Physics/YangMills/YMClayP0BishopRealCarrierInstancesExact.agda
  DASHI/Physics/YangMills/YMClayP0BishopToOriginalWilsonRealWeldExact.agda
  DASHI/Physics/YangMills/YMClayP0OriginalPartitionBishopApartnessExact.agda
)

for source in "${sources[@]}"; do
  test -s "$source" || {
    echo "missing or empty Agda source: $source" >&2
    exit 1
  }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|TERMINATING|NON_COVERING' "$source"; then
    echo "forbidden source-level trust escape in $source" >&2
    exit 1
  fi
  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "unsolved hole in $source" >&2
    exit 1
  fi
done

bash scripts/run_agda29_parallel_check.sh --safe "${sources[@]}"
echo "Original Wilson partition -> Bishop apartness source checked."
