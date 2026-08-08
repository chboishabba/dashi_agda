#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Reuse the stronger published-orbifold/local-module owner rather than
# maintaining a second projector, evaluation, cocycle or weight-one checker.
bash scripts/check_monster_3b_orbifold_local_module_round4.sh

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

assert payload["group_order"] == 2859230155080499200
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
  DASHI/Moonshine/Monster3BKernelCharacterCriterionExact.agda
  DASHI/Moonshine/Monster3BActualKernelCharacterPromotionExact.agda
  DASHI/Moonshine/Monster3BFiniteHeisenbergCommutantExact.agda
  DASHI/Moonshine/Monster3BFiniteStoneVonNeumannMultiplicityExact.agda
  DASHI/Moonshine/Monster3BMultiplicityEvaluationExact.agda
  DASHI/Moonshine/Monster3BActualMultiplicityEvaluationFromRecognitionExact.agda
  DASHI/Moonshine/Monster3BNormalizerCocycleCancellationExact.agda
  DASHI/Moonshine/Monster3BMultiplicityCharacterSafeReconstructionExact.agda
  DASHI/Moonshine/Monster3BActualKernelCharacterRound4Validation.agda
)

for source in "${sources[@]}"; do
  test -s "$source"
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK' "$source"; then
    echo "forbidden trust escape in $source" >&2
    exit 1
  fi
  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "forbidden multiline hole in $source" >&2
    exit 1
  fi
done

require_pattern() {
  local source="$1"
  local pattern="$2"
  if ! grep -F "$pattern" "$source" >/dev/null; then
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  fi
}

character=DASHI/Moonshine/Monster3BKernelCharacterCriterionExact.agda
promotion=DASHI/Moonshine/Monster3BActualKernelCharacterPromotionExact.agda
commutant=DASHI/Moonshine/Monster3BFiniteHeisenbergCommutantExact.agda
stone=DASHI/Moonshine/Monster3BFiniteStoneVonNeumannMultiplicityExact.agda
existing_eval=DASHI/Moonshine/Monster3BMultiplicityEvaluationExact.agda
actual_eval=DASHI/Moonshine/Monster3BActualMultiplicityEvaluationFromRecognitionExact.agda
cocycle=DASHI/Moonshine/Monster3BNormalizerCocycleCancellationExact.agda
safe=DASHI/Moonshine/Monster3BMultiplicityCharacterSafeReconstructionExact.agda
validation=DASHI/Moonshine/Monster3BActualKernelCharacterRound4Validation.agda
reference=Docs/support/reference/Monster3BActualKernelCharacterRound4.md

require_pattern "$character" 'extraspecialCharacterDegreeSquareSumIsOrder'
require_pattern "$character" 'heisenbergNormNumeratorIsExtraspecialOrder'
require_pattern "$character" 'modelConjugateNoncentralTraceIsZero'
require_pattern "$character" 'actualKernelCharacterIdentity'
require_pattern "$character" 'actualCentralZetaTraceAmplitude'
require_pattern "$promotion" 'ActualMN3BKernelStructure'
require_pattern "$promotion" 'actualKernelNoncentralCharacterVanishes'
require_pattern "$promotion" 'actualKernelCentralCharacterIsZeta'
require_pattern "$promotion" 'actualZetaSectorIsNinetyHeisenbergCopies'
require_pattern "$commutant" 'coordinateSeparation'
require_pattern "$commutant" 'difference6Restores'
require_pattern "$commutant" 'offDiagonalCoefficientVanishes'
require_pattern "$commutant" 'diagonalCoefficientIsOrigin'
require_pattern "$commutant" 'schrodingerCommutantIsScalar'
require_pattern "$stone" 'constituentDegreeSumIsHeisenbergTimesCount'
require_pattern "$stone" 'multiplicityForcedToNinety'
require_pattern "$stone" 'actualZetaSectorHasNinetyConstituents'
require_pattern "$existing_eval" 'ActualZetaSectorRecognition'
require_pattern "$actual_eval" 'actualEvaluationLeftInverse'
require_pattern "$actual_eval" 'actualEvaluationRightInverse'
require_pattern "$actual_eval" 'actualEvaluationTranslationEquivariant'
require_pattern "$actual_eval" 'actualMonsterMultiplicityEvaluationIsomorphism'
require_pattern "$cocycle" 'compensatedTensorActionIsHonestOnPureTensors'
require_pattern "$safe" 'TraceAlgebra'
require_pattern "$safe" 'multiplicityCharacterReconstructsAllClasses'
require_pattern "$safe" 'zeroTraceClassCannotUseQuotientAlone'
require_pattern "$safe" 'multiplicityCharacterEqualsTwelvePlusSeventyEight'
require_pattern "$validation" 'extraspecialDegreeBudgetCloses'
require_pattern "$validation" 'finiteSchrodingerCommutantIsScalar'
require_pattern "$validation" 'stoneVonNeumannMultiplicityIsUnique'
require_pattern "$validation" 'actualEvaluationPromotionAvailable'
require_pattern "$reference" 'actual AtlasRep'
require_pattern "$reference" 'pointwise division'

test ! -e DASHI/Moonshine/Monster3BExtraspecialCharacterSignatureExact.agda
test ! -e DASHI/Moonshine/Monster3BProjectiveTensorCocycleExact.agda
test ! -e DASHI/Moonshine/Monster3BActualMultiplicityIntertwinerExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/Monster3BActualKernelCharacterRound4Validation.agda

# Typecheck the generated certificate through the same pinned Agda 2.9 path.
mkdir -p DASHI/Moonshine/Generated
cp build/generated/DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda \
  DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda
trap 'rm -f DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda' EXIT
scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/Generated/Monster3BActualKernelCertificate.agda
