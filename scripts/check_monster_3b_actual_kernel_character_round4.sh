#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_monster_3b_projector_resolution_round3.sh

command -v gap >/dev/null 2>&1 || {
  echo "GAP is required for the actual-kernel tranche" >&2
  exit 1
}

mkdir -p build/generated/DASHI/Moonshine/Generated

python -m py_compile scripts/render_monster_3b_actual_kernel_certificate.py

gap -q scripts/monster_3b_normalizer_restriction.g
gap -q scripts/monster_3b_actual_kernel_structure.g

test -s build/monster_3b_normalizer_restriction.json
test -s build/monster_3b_actual_kernel_structure.json

python scripts/render_monster_3b_actual_kernel_certificate.py \
  build/monster_3b_actual_kernel_structure.json \
  build/monster_3b_normalizer_restriction.json \
  build/monster_3b_actual_kernel_character_certificate.json \
  build/generated/DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda

test -s build/monster_3b_actual_kernel_character_certificate.json
test -s build/generated/DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda

python - <<'PY'
import json
from pathlib import Path

payload = json.loads(Path(
    "build/monster_3b_actual_kernel_character_certificate.json"
).read_text())

assert payload["actual_group_order"] == 2859230155080499200
assert payload["kernel_order"] == 1594323
assert payload["kernel_exponent"] == 3
assert payload["centre_order"] == 3
assert payload["derived_order"] == 3
assert payload["quotient_order"] == 531441
assert payload["centre_orbit_size"] == 2
assert payload["actual_kernel_and_restriction_class_aligned"] is True
assert payload["extraspecial_structure_certified"] is True
assert payload["heisenberg_degree"] == 729
assert payload["heisenberg_multiplicity"] == 90
assert payload["zeta_degree_reconstruction"] == 65610
assert payload["actual_multiplicity_character_computed"] is False
assert payload["twelve_plus_seventy_eight_proved"] is False
PY

sources=(
  DASHI/Moonshine/Monster3BExtraspecialCharacterSignatureExact.agda
  DASHI/Moonshine/Monster3BActualKernelCharacterPromotionExact.agda
  DASHI/Moonshine/Monster3BActualMultiplicityIntertwinerExact.agda
  DASHI/Moonshine/Monster3BProjectiveTensorCocycleExact.agda
  DASHI/Moonshine/Monster3BMultiplicityCharacterSafeReconstructionExact.agda
  DASHI/Moonshine/MoonshineOrbifoldMasslessStateRemovalExact.agda
  DASHI/Moonshine/Monster3BActualKernelCharacterRound4Validation.agda
)

for source in "${sources[@]}"; do
  test -s "$source"
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|TERMINATING|NO_POSITIVITY_CHECK|{-# OPTIONS --unsafe|\{![^}]*!\}' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
done

required_patterns=(
  'extraspecialCharacterDegreeSquareSumIsOrder'
  'heisenbergNormNumeratorIsExtraspecialOrder'
  'ninetyHeisenbergNoncentralValue'
  'actualKernelCharacterIdentity'
  'actualKernelNoncentralCharacterVanishes'
  'actualKernelCentralCharacterIsZeta'
  'actualZetaSectorIsNinetyHeisenbergCopies'
  'actualEvaluationMapInjective'
  'actualEvaluationMapSurjective'
  'actualMonsterLocalModuleIntertwiner'
  'tensorCocycleCancels'
  'multiplicityCharacterReconstructsAllClasses'
  'zeroTraceClassCannotUseQuotientAlone'
  'multiplicityCharacterEqualsTwelvePlusSeventyEight'
  'orbifoldCompletionRemovesWeightOne'
  'impliesFourDimensionalYangMillsGapIsFalse'
)

for pattern in "${required_patterns[@]}"; do
  grep -R -F "$pattern" "${sources[@]}" >/dev/null
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/Monster3BActualKernelCharacterRound4Validation.agda

# Typecheck the generated certificate through the same pinned Agda 2.9 path.
mkdir -p DASHI/Moonshine/Generated
cp build/generated/DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda \
  DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda
trap 'rm -f DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda' EXIT
scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda
