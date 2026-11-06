#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Geometry/GielisBase369FiniteExact.agda
  DASHI/Geometry/GielisBase369NyquistPhase36Exact.agda
  DASHI/Geometry/GielisBase369ExistingOwnersWeldExact.agda
)
for source_file in "${sources[@]}"; do
  [[ -s "$source_file" ]] || { echo "missing Agda source: $source_file" >&2; exit 1; }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--unsafe|TERMINATING|NON_COVERING' "$source_file"; then
    echo "Agda trust escape rejected: $source_file" >&2
    exit 1
  fi
  if grep -Pzoq '(?s)\\{!.*?!\\}' "$source_file"; then
    echo "Agda hole rejected: $source_file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh "${sources[@]}"

python -m pytest -q tests/test_gielis_base369_experiments.py
python scripts/gielis_base369_experiments.py --pde --optics \
  --rays 72 --segments 384 --bounces 4 --controls --torque-objective min > /dev/null
echo "Gielis Base369 finite+numeric cut passed"
