#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ssp15_j_gluing_mathieu_interference_round6.sh

sources=(
  DASHI/Foundations/StratifiedResolutionTowerExact.agda
  DASHI/Biology/IndexedJStratifiedMultiresolutionExact.agda
  DASHI/Biology/SSP369JResolutionBifiltrationExact.agda
  DASHI/Moonshine/SSPJStratifiedQuotientRound7Validation.agda
  DASHI/EverythingSSPJStratifiedQuotientRound7.agda
)

for source in "${sources[@]}"; do
  test -s "$source" || { echo "missing or empty source $source" >&2; exit 1; }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|trustMe|primTrustMe|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
  grep -Pzo '\{!.*?!\}' "$source" >/dev/null && {
    echo "forbidden interaction hole in $source" >&2
    exit 1
  }
done

require_pattern() {
  grep -F "$2" "$1" >/dev/null || {
    echo "missing required marker '$2' in $1" >&2
    exit 1
  }
}

tower=DASHI/Foundations/StratifiedResolutionTowerExact.agda
jmulti=DASHI/Biology/IndexedJStratifiedMultiresolutionExact.agda
bif=DASHI/Biology/SSP369JResolutionBifiltrationExact.agda
validation=DASHI/Moonshine/SSPJStratifiedQuotientRound7Validation.agda
top=DASHI/EverythingSSPJStratifiedQuotientRound7.agda

require_pattern "$tower" 'record ResolutionTower'
require_pattern "$tower" 'record SplitResolutionStructure'
require_pattern "$tower" 'multiscaleCarriesChosenSplit'
require_pattern "$tower" 'record StratifiedProjection'
require_pattern "$tower" 'toyStratifiedProjection'
require_pattern "$tower" 'record InverseLimitPoint'
require_pattern "$tower" 'pullbackConstantOnFibre'
require_pattern "$jmulti" 'decimalSplitJoin'
require_pattern "$jmulti" 'decimalJoinSplit'
require_pattern "$jmulti" 'decimalGrade2'
require_pattern "$jmulti" 'decimalGrade3'
require_pattern "$jmulti" 'decimalRetained2'
require_pattern "$jmulti" 'decimalRetained3'
require_pattern "$jmulti" 'firstCumulativeMatchesJoinedIndexNumerically'
require_pattern "$jmulti" 'decimalAddressInverseLimitIsAutomaticallyTenAdicRingIsFalse'
require_pattern "$jmulti" 'finiteGradeCountSuppliesCompletedHilbertDirectSumIsFalse'
require_pattern "$bif" 'record J369Bifiltration'
require_pattern "$bif" 'coarsenDepthCommutes63'
require_pattern "$bif" 'coarsenDepthCommutes96'
require_pattern "$bif" 'coarsenInclude36Commutes'
require_pattern "$bif" 'coarsenInclude69Commutes'
require_pattern "$bif" 'commutingFiniteBifiltrationProvesTwoInfiniteLimitsCommuteIsFalse'
require_pattern "$validation" 'validationDecimalSplitJoin'
require_pattern "$validation" 'validationAllZeroInverseLimitCoherence'
require_pattern "$validation" 'validationDepthResolutionCommute63'
require_pattern "$validation" 'validationDepthResolutionCommute96'
require_pattern "$top" 'import DASHI.EverythingSSPJGluingMathieuRound6'

mkdir -p artifacts
python3 scripts/classify_agda_substance.py \
  --fail-on-external \
  --output artifacts/ssp15-j-stratified-quotient-multiresolution-round7.json \
  "${sources[@]}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/SSPJStratifiedQuotientRound7Validation.agda \
  DASHI/EverythingSSPJStratifiedQuotientRound7.agda
