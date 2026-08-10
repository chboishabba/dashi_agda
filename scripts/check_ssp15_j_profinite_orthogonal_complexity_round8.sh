#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ssp15_j_stratified_quotient_multiresolution_round7.sh

sources=(
  DASHI/Analysis/NormalizedFibreAveragingExact.agda
  DASHI/Analysis/WeightedCoarseFineOrthogonalExact.agda
  DASHI/Analysis/GlassesProjectionInvolutionExact.agda
  DASHI/Foundations/FilteredExtensionSplittingExact.agda
  DASHI/Foundations/ClaimScopeCertificateExact.agda
  DASHI/Biology/DecimalResidueTowerExact.agda
  DASHI/Biology/DecimalCRTResolutionExact.agda
  DASHI/Biology/TenAdicInverseLimitBridge.agda
  DASHI/Biology/SignedMultiplicityObstructionExact.agda
  DASHI/Biology/FRACTRANWreathControlledSymmetryExact.agda
  DASHI/Biology/SpectralReachabilityComplexityExact.agda
  DASHI/Culture/SignedMultiplicityYinYangBridgeExact.agda
  DASHI/Culture/BeliefFibreReplicationExact.agda
  DASHI/Moonshine/SSPJProfiniteOrthogonalComplexityRound8Validation.agda
  DASHI/EverythingSSPJProfiniteOrthogonalComplexityRound8.agda
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

fibre=DASHI/Analysis/NormalizedFibreAveragingExact.agda
orth=DASHI/Analysis/WeightedCoarseFineOrthogonalExact.agda
glasses=DASHI/Analysis/GlassesProjectionInvolutionExact.agda
filtered=DASHI/Foundations/FilteredExtensionSplittingExact.agda
scope=DASHI/Foundations/ClaimScopeCertificateExact.agda
decimal=DASHI/Biology/DecimalResidueTowerExact.agda
crt=DASHI/Biology/DecimalCRTResolutionExact.agda
tenadic=DASHI/Biology/TenAdicInverseLimitBridge.agda
defect=DASHI/Biology/SignedMultiplicityObstructionExact.agda
controlled=DASHI/Biology/FRACTRANWreathControlledSymmetryExact.agda
complexity=DASHI/Biology/SpectralReachabilityComplexityExact.agda
yinyang=DASHI/Culture/SignedMultiplicityYinYangBridgeExact.agda
belief=DASHI/Culture/BeliefFibreReplicationExact.agda
validation=DASHI/Moonshine/SSPJProfiniteOrthogonalComplexityRound8Validation.agda
top=DASHI/EverythingSSPJProfiniteOrthogonalComplexityRound8.agda

require_pattern "$fibre" 'fibreMassIsOne'
require_pattern "$fibre" 'averagePullback'
require_pattern "$fibre" 'projectionIdempotent'
require_pattern "$orth" 'pullbackAverageAdjoint'
require_pattern "$orth" 'projectionSelfAdjoint'
require_pattern "$orth" 'projectionResidualOrthogonal'
require_pattern "$glasses" 'JInvolutive'
require_pattern "$glasses" 'JPJIsQ'
require_pattern "$glasses" 'JQJIsP'
require_pattern "$glasses" 'inversionDefectIsZero'
require_pattern "$filtered" 'record SplitExtension'
require_pattern "$filtered" 'gradedCountSumIsEleven'
require_pattern "$scope" 'Refutation : Set → Set'
require_pattern "$scope" 'legacyFalseFlagShouldBeReadAsImpossibilityProofIsFalse'
require_pattern "$decimal" 'decodeEncodeResidue'
require_pattern "$decimal" 'encodeDecodeResidue'
require_pattern "$decimal" 'encodePrefixCompatible'
require_pattern "$crt" 'tenPowerFactor'
require_pattern "$crt" 'cardinalFactorBackwardForward'
require_pattern "$crt" 'record CoherentCRTSystem'
require_pattern "$tenadic" 'record TowerEquivalence'
require_pattern "$tenadic" 'decimalResidueTowerEquivalence'
require_pattern "$tenadic" 'splitProductHistory'
require_pattern "$tenadic" 'decimalHistoryToTwoFive'
require_pattern "$defect" 'oneAndTwoHaveSamePresence'
require_pattern "$defect" 'oneAndTwoHaveNonzeroSignedDefect'
require_pattern "$defect" 'twistedAntiSymmetry'
require_pattern "$controlled" 'controlledStep'
require_pattern "$controlled" 'decodeEncodeTriState'
require_pattern "$complexity" 'invariantSeparatesNoReach'
require_pattern "$complexity" 'reachPotentialBound'
require_pattern "$complexity" 'record ComplexityIndexedCarrier'
require_pattern "$complexity" 'record FibreWitnessProblem'
require_pattern "$yinyang" 'swapMultiplicityReversesCandidatePolarity'
require_pattern "$belief" 'beliefLiesInTransitionFibre'
require_pattern "$validation" 'validationFibreMassIsOne'
require_pattern "$validation" 'validationGlassesExchangesPForQ'
require_pattern "$validation" 'validationDecimalPrefixReduction'
require_pattern "$validation" 'validationOccurrenceForgetsMultiplicity'
require_pattern "$validation" 'validationControlledWreathLeft'
require_pattern "$validation" 'validationPotentialBudget'
require_pattern "$top" 'import DASHI.EverythingSSPJStratifiedQuotientRound7'

mkdir -p artifacts
python3 scripts/classify_agda_substance.py \
  --fail-on-external \
  --output artifacts/ssp15-j-profinite-orthogonal-complexity-round8.json \
  "${sources[@]}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/SSPJProfiniteOrthogonalComplexityRound8Validation.agda \
  DASHI/EverythingSSPJProfiniteOrthogonalComplexityRound8.agda
