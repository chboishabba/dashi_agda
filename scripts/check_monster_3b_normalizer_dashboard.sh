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
  elementary_abelian_two_plane_certificate.json
)

for name in "${required[@]}"; do
  test -s "build/monster_3b_dashboard/$name"
done

python - <<'PY'
import json
from pathlib import Path
payload = json.loads(Path(
    "build/monster_3b_dashboard/elementary_abelian_two_plane_certificate.json"
).read_text())
assert payload == {
    "central_lift_order": 27,
    "central_lift_rank": 3,
    "fixed_lagrangian_two_plane_count": 11011,
    "full_isotropic_two_plane_count": 1961279320,
    "full_nonisotropic_two_plane_count": 3922625070,
    "full_symplectic_two_plane_count": 5883904390,
    "regular_character_multiplicity": 81,
    "represented_dimension": 729,
    "translation_character_count": 9,
}
PY

agda_sources=(
  DASHI/Moonshine/Monster3BNormalizerBridge.agda
  DASHI/Moonshine/Monster3BCyclicFourierDyadicBridgeExact.agda
  DASHI/Moonshine/Monster3BHeisenbergMultiplicityExact.agda
  DASHI/Moonshine/Monster3BFiniteHeisenbergGeneratorsExact.agda
  DASHI/Moonshine/Monster3BFiniteHeisenbergPermutationExact.agda
  DASHI/Moonshine/Monster3BElementaryAbelianInvariantExact.agda
  DASHI/Moonshine/Monster3BPhaseTransportExact.agda
  DASHI/Moonshine/MonsterThreeLocalE8LeechBridgeExact.agda
  DASHI/Moonshine/LeechWeightTwo196608BridgeExact.agda
  DASHI/Moonshine/MonsterYangMills196608CrossLaneExact.agda
  DASHI/Moonshine/C3FourierConjugationExact.agda
  DASHI/Moonshine/C3CyclotomicRealDescentExact.agda
  DASHI/Moonshine/C3CyclotomicAmplitudeAlgebraExact.agda
  DASHI/Moonshine/C3RiemannConjugationBridgeExact.agda
  DASHI/Moonshine/SSP15AffineC3TranslationExact.agda
  DASHI/Moonshine/SSP15CMModSevenExact.agda
  DASHI/Moonshine/SSP15PhaseClosure54Exact.agda
  DASHI/Moonshine/MonsterReducedNonaryBoundaryExact.agda
  DASHI/Moonshine/MonsterC3SSP42HighestAlphaValidation.agda
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
  agda -i . -l standard-library \
    DASHI/Moonshine/MonsterC3SSP42HighestAlphaValidation.agda
  agda -i . -l standard-library \
    DASHI/Moonshine/Monster3BHighestAlphaValidation.agda

  if test -s build/generated/DASHI/Moonshine/Generated/Monster3BRestrictionCertificate.agda; then
    agda -i . -i build/generated -l standard-library \
      build/generated/DASHI/Moonshine/Generated/Monster3BRestrictionCertificate.agda
  fi
else
  echo "agda unavailable: skipped kernel check" >&2
fi
