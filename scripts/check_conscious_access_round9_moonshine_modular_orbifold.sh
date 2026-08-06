#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_conscious_access_round8_voa_grade_semantics.sh

files=(
  DASHI/Biology/MoonshineModularFormCoefficientExact.agda
  DASHI/Biology/MoonshineOrbifoldSectorProjectorExact.agda
  DASHI/Biology/MoonshineMonsterLieStringBigradingExact.agda
  DASHI/Biology/MoonshineGriessAutomorphismClassificationExact.agda
  DASHI/Biology/MonsterConstructionRouteComparisonExact.agda
  DASHI/Biology/ConsciousAccessRound9MoonshineModularOrbifoldValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round nine contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'MoonshineModularFormCoefficientExact.agda:jConstantExact'
  'MoonshineModularFormCoefficientExact.agda:jCoefficientOneExact'
  'MoonshineModularFormCoefficientExact.agda:jCoefficientTwoExact'
  'MoonshineModularFormCoefficientExact.agda:moonshineCharacterMatchesNormalizedJPrefix'
  'MoonshineOrbifoldSectorProjectorExact.agda:positivePlusNegativeFirst'
  'MoonshineOrbifoldSectorProjectorExact.agda:positiveProjectionIdempotentFirst'
  'MoonshineOrbifoldSectorProjectorExact.agda:negativeProjectionSwapOddFirst'
  'MoonshineMonsterLieStringBigradingExact.agda:oneOneRootMultiplicityExact'
  'MoonshineMonsterLieStringBigradingExact.agda:sameProductGivesSameSampleMultiplicity'
  'MoonshineGriessAutomorphismClassificationExact.agda:automorphismFixesUnit'
  'MoonshineGriessAutomorphismClassificationExact.agda:halfOmegaActsAsUnit'
  'MoonshineGriessAutomorphismClassificationExact.agda:restrictVOAAutomorphismToGriess'
  'MonsterConstructionRouteComparisonExact.agda:griessRouteIsNotVOARoute'
  'MonsterConstructionRouteComparisonExact.agda:borcherdsAddsGeneralizedKacMoodyStructure'
  'MonsterConstructionRouteComparisonExact.agda:restrictionBridge'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Biology/$file"
done

grep -q '10.1073/pnas.81.10.3256' DASHI/Biology/MoonshineModularFormCoefficientExact.agda
grep -q '10.1007/s002200000242' DASHI/Biology/MoonshineOrbifoldSectorProjectorExact.agda
grep -q '10.1016/0001-8708(90)90067-W' DASHI/Biology/MoonshineMonsterLieStringBigradingExact.agda
grep -q '10.1007/BF01389186' DASHI/Biology/MoonshineGriessAutomorphismClassificationExact.agda
grep -q '10.1112/blms/11.3.308' DASHI/Biology/MonsterConstructionRouteComparisonExact.agda

grep -q 'finiteCoefficientConvolutionDoesNotProveSL2ZModularity' DASHI/Biology/MoonshineModularFormCoefficientExact.agda
grep -q 'fixed-point algebra' DASHI/Biology/MoonshineOrbifoldSectorProjectorExact.agda
grep -q 'finiteMultiplicityPrefixDoesNotConstructBRSTCohomology' DASHI/Biology/MoonshineMonsterLieStringBigradingExact.agda
grep -q 'converseExtensionRequiresSeparateTheorem' DASHI/Biology/MoonshineGriessAutomorphismClassificationExact.agda
grep -q 'equalDimensionDoesNotIdentifyRoutes' DASHI/Biology/MonsterConstructionRouteComparisonExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound9MoonshineModularOrbifoldValidation.agda
