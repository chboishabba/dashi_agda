#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_monster_3b_normalizer_dashboard.sh

sources=(
  DASHI/Moonshine/Monster3BCentredProbeCoreSelectorExact.agda
  DASHI/Moonshine/Monster3BMaximalRegularCoreExact.agda
  DASHI/Moonshine/Monster3BConformalLinePlacementExact.agda
  DASHI/Moonshine/Monster3BFiniteProjectorModelExact.agda
  DASHI/Moonshine/Monster3BFiniteWeightProjectorExact.agda
  DASHI/Moonshine/Monster3BMultiplicityCharacterProjectorExact.agda
  DASHI/Moonshine/Monster3BHighestAlphaValidation.agda
)

for source in "${sources[@]}"; do
  test -s "$source"
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|TERMINATING|NO_POSITIVITY_CHECK|{-# OPTIONS --unsafe' "$source"; then
    echo "forbidden trust escape in $source" >&2
    exit 1
  fi
done

required_patterns=(
  'centredProbeDefectFactorization'
  'maximalRegularCore = 65610'
  'dyadicUniformCore = 65536'
  'dyadicCoreCanonicallySelectedByMonsterActionIsFalse'
  'canonicalMaximalCoreDecomposition'
  'maximalRegularCoreDominatesEveryUniformCore'
  'moonshineWeightTwoSplitsConformalPlusMonster'
  'conformalLineFixedByMonsterLevel = standardImported'
  'evaluationLeftInverse'
  'evaluationRightInverse'
  'evaluationTranslationEquivariant'
  'zetaModelDimensionIs65610'
  'weightProjectorCoefficientIdempotent'
  'translatedProjectorCovariant'
  'allTranslatedProjectorsResolveActualSectorIdentityIsFalse'
  'multiplicityTraceProjectorFormula'
  'multiplicityTwelvePlusSeventyEight'
  'actualMultiplicityCharacterCertifiedIsFalse'
)

for pattern in "${required_patterns[@]}"; do
  grep -R -F "$pattern" "${sources[@]}" >/dev/null
done

grep -F '729 * 90 = 65610' Docs/support/reference/Monster3BProjectorCoreRound2.md >/dev/null
grep -F 'dyadicCoreCanonicallySelectedByMonsterAction = false' Docs/support/reference/Monster3BProjectorCoreRound2.md >/dev/null
grep -F 'maximal regular `C3` core' Docs/support/reference/Monster3BProjectorCoreRound2.md >/dev/null

if command -v agda >/dev/null 2>&1; then
  agda -i . -l standard-library DASHI/Moonshine/Monster3BHighestAlphaValidation.agda
else
  echo "agda unavailable: skipped kernel check" >&2
fi
