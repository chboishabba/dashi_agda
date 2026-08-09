#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ssp15_modular_character_projection_round5.sh

sources=(
  DASHI/Biology/EisensteinNineRingInterferenceExact.agda
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
  if [ ! -s "$source" ]; then
    echo "missing or empty source $source" >&2
    exit 1
  fi
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|trustMe|primTrustMe|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
  if grep -Pzo '\{!.*?!\}' "$source" >/dev/null; then
    echo "forbidden interaction hole in $source" >&2
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

gluing=DASHI/Biology/IndexedJExternalGluingExact.agda
half=DASHI/Biology/HalfChartNineRingQuotientExact.agda
eisenstein=DASHI/Biology/EisensteinNineRingInterferenceExact.agda
spiral=DASHI/Biology/IteratedPointedAttachmentSpiralExact.agda
monster=DASHI/Moonshine/Monster196884FibreInterferenceExact.agda
mathieu=DASHI/Moonshine/MathieuStabilizerTowerExact.agda
divisor=DASHI/Moonshine/MathieuDivisorLatticeExact.agda
path=DASHI/Moonshine/MathieuDivisorPathInterferenceExact.agda
integration=DASHI/Moonshine/MathieuJTransportIntegrationExact.agda
validation=DASHI/Moonshine/SSPJGluingMathieuRound6Validation.agda
top=DASHI/EverythingSSPJGluingMathieuRound6.agda

require_pattern "$gluing" 'DOI: 10.1007/978-1-4757-4721-8.'
require_pattern "$gluing" 'oneAndTenCloseToSameSeam'
require_pattern "$gluing" 'localAndTransportedRepresentSameExternalPoint'
require_pattern "$gluing" 'joinedAddressIndexIsEleven'
require_pattern "$gluing" 'finiteAttachmentProvesCategoricalPushoutUniversalPropertyIsFalse'
require_pattern "$half" 'baseEndpointsGlue'
require_pattern "$half" 'unfoldedCountIsTen'
require_pattern "$half" 'quotientCountIsNine'
require_pattern "$half" 'fiveMeaningsAreDistinct'
require_pattern "$eisenstein" 'DOI: 10.1007/978-1-4612-0853-2.'
require_pattern "$eisenstein" 'qOne = + 1 / 1'
require_pattern "$eisenstein" 'qTwo = + 2 / 1'
require_pattern "$eisenstein" 'qMinusOne = 0ℚ - qOne'
require_pattern "$eisenstein" 'normPolarization'
require_pattern "$eisenstein" 'threePhaseTotalMassCancels'
require_pattern "$eisenstein" 'hostGuestInterferenceIdentity'
require_pattern "$eisenstein" 'vacantOrientationsCollapse'
require_pattern "$eisenstein" 'occupiedOrientationsRemainDistinct'
require_pattern "$eisenstein" 'nineAddressFieldCountIs19683'
require_pattern "$spiral" 'oneTenProjectedSeam'
require_pattern "$spiral" 'tenElevenAdvanceDepth'
require_pattern "$spiral" 'formalismIsAttributedToMarxIsFalse'
require_pattern "$monster" 'factorizedIdentity'
require_pattern "$monster" 'fibreInterferenceTotalIs196884'
require_pattern "$monster" 'matchesExistingMoonshineV2Dimension'
require_pattern "$monster" 'factorsConstructMonsterSubmodulesIsFalse'
require_pattern "$mathieu" 'DOI: 10.1007/978-1-4612-0731-3.'
require_pattern "$mathieu" 'm11OrderAsSuccessiveOrbits'
require_pattern "$mathieu" 'm12OrderAsSuccessiveOrbits'
require_pattern "$mathieu" 'record OrbitStabilizerArithmeticWitness'
require_pattern "$mathieu" 'record MathieuStepArithmeticWitness'
require_pattern "$mathieu" 'stepArithmeticWitness'
require_pattern "$mathieu" 'atlasReportedM8IsNotD4'
require_pattern "$mathieu" 'actualGroupActionsConstructedHereIsFalse'
require_pattern "$mathieu" 'arithmeticWitnessContainsActionLawsIsFalse'
require_pattern "$divisor" 'DOI: 10.1090/coll/025.'
require_pattern "$divisor" 'm12DivisorNodeCount'
require_pattern "$divisor" 'm11DivisorNodeCount'
require_pattern "$divisor" 'centralizerPlusClassIsM12'
require_pattern "$divisor" 'chooseTwelveFourIs495'
require_pattern "$divisor" 'historiesShareEndpoint'
require_pattern "$path" 'nodeInterferenceIdentity'
require_pattern "$path" 'canonicalNodeIntensityIsOne'
require_pattern "$path" 'canonicalPathCrossIsMinusOne'
require_pattern "$path" 'divisorIncidenceDeterminesAmplitudeIsFalse'
require_pattern "$integration" 'mathieuTenOrbitOrderLaw'
require_pattern "$integration" 'mathieuElevenOrbitOrderLaw'
require_pattern "$integration" 'canonicalNineToTenAnalogy'
require_pattern "$integration" 'transportedGuestIsClassicalModularJIsFalse'
require_pattern "$validation" 'validationZeroOneSeam'
require_pattern "$validation" 'validationMonsterSplit'
require_pattern "$validation" 'validationM8NotD4'
require_pattern "$validation" 'validationChooseTwelveFour'
require_pattern "$validation" 'validationDecoratedPathsReachSix'
require_pattern "$validation" 'validationDecoratedPathNodeIntensity'
require_pattern "$validation" 'validationDecoratedPathCrossTerm'
require_pattern "$top" 'import DASHI.Moonshine.MathieuDivisorPathInterferenceExact'
require_pattern "$top" 'import DASHI.Moonshine.SSPJGluingMathieuRound6Validation'

mkdir -p artifacts
python3 scripts/classify_agda_substance.py \
  --fail-on-external \
  --output artifacts/ssp15-j-gluing-mathieu-interference-round6.json \
  "${sources[@]}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/SSPJGluingMathieuRound6Validation.agda \
  DASHI/EverythingSSPJGluingMathieuRound6.agda
