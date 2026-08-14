#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ -x scripts/check_crypto_blue_team_adversary_closure_round16.sh ]]; then
  scripts/check_crypto_blue_team_adversary_closure_round16.sh
fi

FILES=(
  DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
  DASHI/Crypto/MLKEMNTTPriorCutNoGoExact.agda
  DASHI/Crypto/MLKEMNTTParityBlockPriorExact.agda
  DASHI/Crypto/MLKEMNTTCombinedCouplingConnectivityExact.agda
  DASHI/Crypto/MLKEMCandidateMoveFanoutExact.agda
  DASHI/Crypto/MLKEMBaseCaseConditionedResidualExact.agda
  DASHI/Crypto/ConditionedResidualAmbiguityRegressionExact.agda
  DASHI/Crypto/ConditionalMateAmbiguityExact.agda
  DASHI/Crypto/ConditionalReconciliationSearchExact.agda
  DASHI/Crypto/ObservationAcquisitionCostExact.agda
  DASHI/Crypto/KeyConfirmationObservationRefinementExact.agda
  DASHI/Crypto/MLKEMImplicitRejectProtocolObservationExact.agda
  DASHI/Crypto/MLKEMImplicitRejectTimingCompositionExact.agda
  DASHI/Crypto/FiniteMLWEConfirmationObservationExact.agda
  DASHI/Crypto/ObservationSeparatorGeometryExact.agda
  DASHI/Crypto/ProtectedLabelSearchGeometryExact.agda
  DASHI/Crypto/SearchGraphEmbeddingDistortionExact.agda
  DASHI/Crypto/GrayPathTransitionOptimalExact.agda
  DASHI/Crypto/FiniteMLWETransitionGeometryExact.agda
  DASHI/Crypto/IncrementalResidualTraversalExact.agda
  DASHI/Crypto/CryptoRepresentationParetoExact.agda
  DASHI/Crypto/AdaptiveCandidateResidualWidthExact.agda
  DASHI/Crypto/ConditionalResidualRateExact.agda
  DASHI/Crypto/FiniteGuessingProbabilityExact.agda
  DASHI/Crypto/RepresentationLeakageGeometryExact.agda
  DASHI/Crypto/BlueTeamSearchObservationRound17.agda
  DASHI/EverythingTerminalisationProvenanceSymmetryRound10.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'algorithm9StageCount' DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
grep -q 'zeroIndex128' DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
grep -q 'sevenStageScalarDependencyWidth' DASHI/Crypto/MLKEMNTTDataflowCouplingExact.agda
grep -q 'combinedCouplingHasNoNontrivialDisconnectedCut' DASHI/Crypto/MLKEMNTTCombinedCouplingConnectivityExact.agda
grep -q 'mlKem1024PublicResidualMoveFanout' DASHI/Crypto/MLKEMCandidateMoveFanoutExact.agda
grep -q 'conditionedResidual0' DASHI/Crypto/MLKEMBaseCaseConditionedResidualExact.agda
grep -q 'conditionedResidual1' DASHI/Crypto/MLKEMBaseCaseConditionedResidualExact.agda
grep -q 'conditionedEquationLeavesTwoPlausibleSecrets' DASHI/Crypto/ConditionedResidualAmbiguityRegressionExact.agda
grep -q 'noUniqueMateFromConditioningAlone' DASHI/Crypto/ConditionalMateAmbiguityExact.agda
grep -q 'leftCandidateGivesGlobal' DASHI/Crypto/ConditionalReconciliationSearchExact.agda
grep -q 'labConfirmationCost2NetGain' DASHI/Crypto/FiniteMLWEConfirmationObservationExact.agda
grep -q 'separatorObservationGain' DASHI/Crypto/ObservationSeparatorGeometryExact.agda
grep -q 'beneficialGeometryGain' DASHI/Crypto/ProtectedLabelSearchGeometryExact.agda
grep -q 'grayEmbeddingDistortionIs3' DASHI/Crypto/SearchGraphEmbeddingDistortionExact.agda
grep -q 'positivePathCostAtLeastEdgeCount' DASHI/Crypto/GrayPathTransitionOptimalExact.agda
grep -q 'grayAttainsPath4LowerBound' DASHI/Crypto/GrayPathTransitionOptimalExact.agda
grep -q 'sameCandidatesSameRateDifferentTransitionCost' DASHI/Crypto/FiniteMLWETransitionGeometryExact.agda
grep -q 'grayTraversalSavesThreeWorkUnits' DASHI/Crypto/IncrementalResidualTraversalExact.agda
grep -q 'grayWeaklyDominatesBinary' DASHI/Crypto/CryptoRepresentationParetoExact.agda
grep -q 'observationShrinksResidualWidth' DASHI/Crypto/AdaptiveCandidateResidualWidthExact.agda
grep -q 'adaptiveSavesThreeBitMassUnits' DASHI/Crypto/ConditionalResidualRateExact.agda
grep -q 'statisticalGainDoesNotImplySearchGain' DASHI/Crypto/FiniteGuessingProbabilityExact.agda
grep -q 'sameLogicalTransitionDifferentPhysicalObservation' DASHI/Crypto/RepresentationLeakageGeometryExact.agda

grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMBaseCaseConditionedResidualExact.agda
grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMCandidateMoveFanoutExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/Crypto/BlueTeamSearchObservationRound17.agda
else
  echo "agda unavailable: structural/fail-closed round-17 geometry scan completed; no kernel-clean claim"
fi
