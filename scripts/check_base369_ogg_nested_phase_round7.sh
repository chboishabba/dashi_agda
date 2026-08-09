#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_base369_process_hyperfabric_round6.sh

sources=(
  DASHI/Foundations/Base369NonaryTritSquareExact.agda
  DASHI/Foundations/Base369CompletedRelationalDigitExact.agda
  DASHI/Foundations/Base369FiveModePhaseQuotientExact.agda
  DASHI/Foundations/Base369RelationalSymmetryRealisationExact.agda
  DASHI/Foundations/Base369PhaseCompletionAndNestedEvaluationExact.agda
  DASHI/Moonshine/MonsterOggNonarySSPTritBridgeExact.agda
  DASHI/Moonshine/MonsterC3CyclotomicEvaluationExact.agda
  DASHI/Moonshine/Monster3BBalancedRegularFibreExact.agda
  DASHI/Moonshine/MonsterOggPrimaryDepthAndNestedEigenCarrierExact.agda
  DASHI/Moonshine/MonsterFivePrimaryRelationalModelBoundaryExact.agda
  DASHI/Foundations/Base369OggNestedPhaseRound7Validation.agda
  DASHI/EverythingBase369OggNestedPhaseRound7.agda
)

for source in "${sources[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing or empty source: $source" >&2
    exit 1
  fi

  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
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

square=DASHI/Foundations/Base369NonaryTritSquareExact.agda
completed=DASHI/Foundations/Base369CompletedRelationalDigitExact.agda
five=DASHI/Foundations/Base369FiveModePhaseQuotientExact.agda
phase=DASHI/Foundations/Base369PhaseCompletionAndNestedEvaluationExact.agda
bridge=DASHI/Moonshine/MonsterOggNonarySSPTritBridgeExact.agda
cyclo=DASHI/Moonshine/MonsterC3CyclotomicEvaluationExact.agda
fibre=DASHI/Moonshine/Monster3BBalancedRegularFibreExact.agda
nested=DASHI/Moonshine/MonsterOggPrimaryDepthAndNestedEigenCarrierExact.agda
fiveBoundary=DASHI/Moonshine/MonsterFivePrimaryRelationalModelBoundaryExact.agda
validation=DASHI/Foundations/Base369OggNestedPhaseRound7Validation.agda
aggregate=DASHI/EverythingBase369OggNestedPhaseRound7.agda

require_pattern "$square" 'nonaryDigitRoundTrip'
require_pattern "$square" 'tritSquareRoundTrip'
require_pattern "$square" 'complementReversesLowTrit'
require_pattern "$completed" 'emptyZeroDigit'
require_pattern "$completed" 'completedNineDigit'
require_pattern "$completed" 'overflowAdvancesScale'
require_pattern "$five" 'pointedNonaryRoundTrip'
require_pattern "$five" 'orientedModeRoundTrip'
require_pattern "$five" 'identityOrientationDuplicationCollapsed'
require_pattern "$phase" 'promotionRetainsFineFibre'
require_pattern "$bridge" 'primeAboveThreeResidueTritNonneutral'
require_pattern "$bridge" 'threeResidueTritNeutral'
require_pattern "$bridge" 'complementReversesResidueTrit'
require_pattern "$bridge" 'modeOrientationRecoversResidueTrit'
require_pattern "$cyclo" 'completeRegularPhaseOrbitCancels'
require_pattern "$cyclo" 'monster3BGeneratorEvaluation'
require_pattern "$fibre" 'monster3BIdentityEvaluationIs196883'
require_pattern "$fibre" 'monster3BNontrivialEvaluationIs53'
require_pattern "$fibre" 'monster3BConformalTraceIs54'
require_pattern "$nested" 'oddPhaseDecompositionExact'
require_pattern "$nested" 'PrimeRelationalCell'
require_pattern "$nested" 'FrickeEigenInversionBridge'
require_pattern "$nested" 'actualOggNestedCarrierConstructedIsFalse'
require_pattern "$fiveBoundary" 'observerIntertwines'
require_pattern "$fiveBoundary" 'actualFiveLocalCarrierIdentifiedIsFalse'
require_pattern "$fiveBoundary" 'actualNineChannelObserverConstructedIsFalse'
require_pattern "$validation" 'completeC3RegularOrbitCancelsExactly'
require_pattern "$validation" 'phasePromotionRetainsFineFibre'
require_pattern "$aggregate" 'MonsterC3CyclotomicEvaluationExact'
require_pattern "$aggregate" 'MonsterFivePrimaryRelationalModelBoundaryExact'

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Base369OggNestedPhaseRound7Validation.agda \
  DASHI/EverythingBase369OggNestedPhaseRound7.agda \
  DASHI/EverythingMonster3BCentralCharacterInertiaRound5.agda
