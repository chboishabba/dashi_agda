#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python -m py_compile scripts/monster_3b_structural_dashboard.py
python scripts/monster_3b_structural_dashboard.py \
  --output build/monster_3b_dashboard

required=(
  extraspecial_plus_minus_phase_sheet.png
  generator_to_invariant_dashboard.png
  heisenberg_weyl_phase_portrait.png
  heisenberg_times_12_plus_78.png
  orbit_length_sheet.png
)

for name in "${required[@]}"; do
  test -s "build/monster_3b_dashboard/$name"
done

if command -v gap >/dev/null 2>&1; then
  mkdir -p build
  gap -q scripts/monster_3b_normalizer_restriction.g
  test -s build/monster_3b_normalizer_restriction.json
  python scripts/monster_3b_structural_dashboard.py \
    --restriction-json build/monster_3b_normalizer_restriction.json \
    --output build/monster_3b_dashboard
  test -s build/monster_3b_dashboard/mn3b_actual_restriction_sheet.png
else
  echo "gap unavailable: skipped CTblLib restriction; structural dashboards passed" >&2
fi

if command -v agda >/dev/null 2>&1; then
  agda -i . DASHI/Moonshine/Monster3BNormalizerBridge.agda
else
  echo "agda unavailable: skipped kernel check" >&2
fi
