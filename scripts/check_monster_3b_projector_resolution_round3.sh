#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_monster_3b_projector_core_round2.sh

sources=(
  DASHI/Moonshine/Monster3BModelProjectorResolutionExact.agda
  DASHI/Moonshine/Monster3BModelStoneVonNeumannRecognitionExact.agda
  DASHI/Moonshine/Monster3BProjectorResolutionRound3Validation.agda
)

for source in "${sources[@]}"; do
  test -s "$source"
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|TERMINATING|NO_POSITIVITY_CHECK|{-# OPTIONS --unsafe|\{![^}]*!\}' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
done

required_patterns=(
  'projectorCoefficientOnOwnWeight'
  'explicitlyDifferentWeightAnnihilatesBasis'
  'ownAndDifferentProjectorsArePointwiseOrthogonal'
  'canonicalModelProjectorResolution'
  'modelResolutionDimensionIs65610'
  'canonicalFiniteEvaluationIsomorphism'
  'evaluationMapIsETranslationEquivariant'
  'standardTranslationHasNoFixedX6Point'
  'standardTranslationHasNoFixedModelBasis'
  'actualExtraspecialKernelActionIdentifiedIsFalse'
  'actualRestrictionIsNinetyHeisenbergCopiesIsFalse'
)

for pattern in "${required_patterns[@]}"; do
  grep -R -F "$pattern" "${sources[@]}" >/dev/null
done

if command -v agda >/dev/null 2>&1; then
  agda -i . -l standard-library \
    DASHI/Moonshine/Monster3BProjectorResolutionRound3Validation.agda
else
  echo "agda unavailable: skipped kernel check" >&2
fi
