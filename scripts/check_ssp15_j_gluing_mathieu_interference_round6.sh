#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ssp15_modular_character_projection_round5.sh

sources=(
  DASHI/Biology/EisensteinNineRingInterferenceExact.agda
  DASHI/Biology/EisensteinThreeSixSymmetryExact.agda
  DASHI/Biology/HalfChartNineRingQuotientExact.agda
  DASHI/Biology/IndexedJExternalGluingExact.agda
  DASHI/Biology/IteratedPointedAttachmentSpiralExact.agda
  DASHI/Moonshine/MathieuDivisorLatticeExact.agda
  DASHI/Moonshine/MathieuDivisorPathInterferenceExact.agda
  DASHI/Moonshine/MathieuJTransportIntegrationExact.agda
  DASHI/Moonshine/MathieuStabilizerTowerExact.agda
  DASHI/Moonshine/Monster196884FibreInterferenceExact.agda
  DASHI/Moonshine/SSPJGluingMathieuRound6Validation.agda
  DASHI/EverythingSSPJGluingMathieuRound6.agda
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

eisenstein=DASHI/Biology/EisensteinNineRingInterferenceExact.agda
threeSix=DASHI/Biology/EisensteinThreeSixSymmetryExact.agda
mathieu=DASHI/Moonshine/MathieuStabilizerTowerExact.agda
validation=DASHI/Moonshine/SSPJGluingMathieuRound6Validation.agda
top=DASHI/EverythingSSPJGluingMathieuRound6.agda

require_pattern "$eisenstein" 'normPolarization'
require_pattern "$eisenstein" 'threePhaseTotalMassCancels'
require_pattern "$threeSix" 'threePhaseCycleCloses'
require_pattern "$threeSix" 'eisensteinUnitCountIsSix'
require_pattern "$threeSix" 'zeroResultantMeansNoAlternativesExistIsFalse'
require_pattern "$mathieu" 'fallingFactorial'
require_pattern "$mathieu" 'm11SharpFourOrderWitness'
require_pattern "$mathieu" 'm12SharpFiveOrderWitness'
require_pattern "$mathieu" 'm11OrderFromSharpFourTransitivity'
require_pattern "$mathieu" 'm12OrderFromSharpFiveTransitivity'
require_pattern "$mathieu" 'threePointStabilizerOrderInM11IsEight'
require_pattern "$mathieu" 'mathieuEightDoesNotComeFromD4'
require_pattern "$mathieu" 'factorEightComesFromD4GridSymmetryIsFalse'
require_pattern "$mathieu" 'divisorLatticeNeededToDeriveOrdersIsFalse'
require_pattern "$validation" 'validationM11SharpFourOrder'
require_pattern "$validation" 'validationM12SharpFiveOrder'
require_pattern "$validation" 'validationSixEisensteinUnits'
require_pattern "$top" 'import DASHI.Biology.EisensteinThreeSixSymmetryExact'

mkdir -p artifacts
python3 scripts/classify_agda_substance.py \
  --fail-on-external \
  --output artifacts/ssp15-j-gluing-mathieu-interference-round6.json \
  "${sources[@]}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/SSPJGluingMathieuRound6Validation.agda \
  DASHI/EverythingSSPJGluingMathieuRound6.agda
