#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

mkdir -p build/monster_3b_dashboard

python -m py_compile \
  scripts/monster_3b_structural_dashboard.py \
  scripts/check_monster_3b_heisenberg_model.py \
  scripts/render_monster_3b_certificate.py

python scripts/check_monster_3b_heisenberg_model.py \
  --output build/monster_3b_heisenberg_model_certificate.json

test -s build/monster_3b_heisenberg_model_certificate.json

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

agda_sources=(
  DASHI/Moonshine/Monster3BNormalizerBridge.agda
  DASHI/Moonshine/Monster3BCyclicFourierDyadicBridgeExact.agda
  DASHI/Moonshine/Monster3BHeisenbergMultiplicityExact.agda
  DASHI/Moonshine/Monster3BPhaseTransportExact.agda
  DASHI/Moonshine/MonsterThreeLocalE8LeechBridgeExact.agda
  DASHI/Moonshine/LeechWeightTwo196608BridgeExact.agda
  DASHI/Moonshine/Monster3BHighestAlphaValidation.agda
)

for source in "${agda_sources[@]}"; do
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|TERMINATING|NO_POSITIVITY_CHECK' "$source"; then
    echo "forbidden trust escape in $source" >&2
    exit 1
  fi
done

if command -v gap >/dev/null 2>&1; then
  gap -q scripts/monster_3b_normalizer_restriction.g
  test -s build/monster_3b_normalizer_restriction.json

  python scripts/render_monster_3b_certificate.py \
    build/monster_3b_normalizer_restriction.json \
    build/generated/DASHI/Moonshine/Generated/Monster3BRestrictionCertificate.agda

  test -s build/generated/DASHI/Moonshine/Generated/Monster3BRestrictionCertificate.agda

  python scripts/monster_3b_structural_dashboard.py \
    --restriction-json build/monster_3b_normalizer_restriction.json \
    --output build/monster_3b_dashboard
  test -s build/monster_3b_dashboard/mn3b_actual_restriction_sheet.png
else
  echo "gap unavailable: skipped CTblLib restriction certificate" >&2
fi

if command -v agda >/dev/null 2>&1; then
  agda -i . DASHI/Moonshine/Monster3BHighestAlphaValidation.agda

  if test -s build/generated/DASHI/Moonshine/Generated/Monster3BRestrictionCertificate.agda; then
    agda -i . -i build/generated \
      build/generated/DASHI/Moonshine/Generated/Monster3BRestrictionCertificate.agda
  fi
else
  echo "agda unavailable: skipped kernel check" >&2
fi
