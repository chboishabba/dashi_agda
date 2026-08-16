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
  DASHI/Crypto/MLKEMLocalityAreaInvariantExact.agda
  DASHI/Crypto/MLKEMButterflyStageLocalityInvariantExact.agda
  DASHI/Crypto/MLKEMNTTSingularBudgetUncertaintyExact.agda
  DASHI/Crypto/MLKEMNTTLocalOutcomeBudgetExact.agda
  DASHI/Crypto/MLKEMNTTLocalMatrixOutcomeClassifierExact.agda
  DASHI/Crypto/MLKEMNTTLocalLeftInverseZeroReflectionExact.agda
  DASHI/Crypto/MLKEMBaseCaseAdjugateInverseExact.agda
  DASHI/Crypto/MLKEMBaseCaseNormInverseBridgeExact.agda
  DASHI/Crypto/MLKEMBaseCaseNonsquareNormSeparationExact.agda
  DASHI/Crypto/MLKEMFIPS203GammaNonsquareTransportExact.agda
  DASHI/Crypto/MLKEMFIPS203F3329ArithmeticExact.agda
  DASHI/Crypto/MLKEMUncertaintyTransitionCostBridgeExact.agda
  DASHI/Crypto/MLKEMProtectedLabelUncertaintyEdgeExact.agda
  DASHI/Crypto/MLKEMSupportUncertaintyRuntimeNoGoExact.agda
  DASHI/Crypto/MLKEMButterflyUncertaintyWorkFrontierExact.agda
  DASHI/Crypto/MLKEMExactResidualTouchLowerBoundExact.agda
  DASHI/Crypto/MLKEMResidualTouchPathLowerBoundExact.agda
  DASHI/Crypto/MLKEMUncertaintyDecisionTreeStrengthBoundaryExact.agda
  DASHI/Crypto/MLKEMTouchInformationNoGoExact.agda
  DASHI/Crypto/MLKEMBoundedReadoutInformationFrontierExact.agda
  DASHI/Crypto/MLKEMProtectedLabelReadoutFactorisationExact.agda
  DASHI/Crypto/MLKEMFiniteStateTranscriptCapacityExact.agda
  DASHI/Crypto/MLKEMBoundedCellTranscriptCapacityExact.agda
  DASHI/Crypto/MLKEMUpdateCapacityDichotomyExact.agda
  DASHI/Crypto/MLKEMFIPS203ProtectedSecretCapacityExact.agda
  DASHI/Crypto/MLKEMFIPS203UpdateCapacityResourceExact.agda
  DASHI/Crypto/MLKEMFinitePriorSuccessMassExact.agda
  DASHI/Crypto/MLKEMFIPS203CBDPriorSuccessBoundExact.agda
  DASHI/Crypto/MLKEMFIPS203AverageSuccessResourceExact.agda
  DASHI/Crypto/MLKEMOppositeResidueParityDecompositionExact.agda
  DASHI/Crypto/MLKEMOppositeResidueParityFibreFactorisationExact.agda
  DASHI/Crypto/MLKEMNTTPair03CubicRootFactorReductionExact.agda
  DASHI/Crypto/MLKEMNTTPair03ReducedKernelCertificateExact.agda
  DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
  DASHI/Crypto/MLKEMBaseCaseConditionedResidualExact.agda
  DASHI/Crypto/ConditionedResidualAmbiguityRegressionExact.agda
  DASHI/Crypto/ConditionalMateAmbiguityExact.agda
  DASHI/Crypto/ConditionalReconciliationSearchExact.agda
  DASHI/Crypto/MLKEMNTTActualCBD2ScalarCollisionExact.agda
  DASHI/Crypto/MLKEMNTTActualCBD2SliceCouplingExact.agda
  DASHI/Crypto/MLKEMNTTActualCBD2TwoScalarRefinementExact.agda
  DASHI/Crypto/MLKEMNTTActualCBD2FullTripleListProfileExact.agda
  DASHI/Crypto/MLKEMNTTActualCBD2ConditionalListMassExact.agda
  DASHI/Crypto/FiniteMLWEListDecodingGeometryExact.agda
  DASHI/Crypto/ObservationAcquisitionCostExact.agda
  DASHI/Crypto/KeyConfirmationObservationRefinementExact.agda
  DASHI/Crypto/MLKEMImplicitRejectProtocolObservationExact.agda
  DASHI/Crypto/MLKEMImplicitRejectTimingCompositionExact.agda
  DASHI/Crypto/FiniteMLWEConfirmationObservationExact.agda
  DASHI/Crypto/ObservationSeparatorGeometryExact.agda
  DASHI/Crypto/AttackerObservationLanguageRefinementExact.agda
  DASHI/Crypto/RepresentationSecurityGameExact.agda
  DASHI/Crypto/ProtectedLabelSearchGeometryExact.agda
  DASHI/Crypto/SearchGraphEmbeddingDistortionExact.agda
  DASHI/Crypto/GrayPathTransitionOptimalExact.agda
  DASHI/Crypto/CBD2MixedRadixGrayTraversalExact.agda
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
grep -q 'combinedCouplingHasNoNontrivialDisconnectedCut' DASHI/Crypto/MLKEMNTTCombinedCouplingConnectivityExact.agda
grep -q 'mlKem1024PublicResidualMoveFanout' DASHI/Crypto/MLKEMCandidateMoveFanoutExact.agda
grep -q 'mlKem512AreasEqual' DASHI/Crypto/MLKEMLocalityAreaInvariantExact.agda
grep -q 'mlKem1024AllStagesEqual' DASHI/Crypto/MLKEMButterflyStageLocalityInvariantExact.agda
grep -q 'singularBudgetUncertainty128' DASHI/Crypto/MLKEMNTTSingularBudgetUncertaintyExact.agda
grep -q 'activeCountWithinBudget' DASHI/Crypto/MLKEMNTTLocalOutcomeBudgetExact.agda
grep -q 'leftInverseReflectsZero' DASHI/Crypto/MLKEMNTTLocalLeftInverseZeroReflectionExact.agda
grep -q 'adjugateBaseCaseIdentity' DASHI/Crypto/MLKEMBaseCaseAdjugateInverseExact.agda
grep -q 'normSeparatedBaseCaseLeftInverse' DASHI/Crypto/MLKEMBaseCaseNormInverseBridgeExact.agda
grep -q 'nonsquareSeparatesNorm' DASHI/Crypto/MLKEMBaseCaseNonsquareNormSeparationExact.agda
grep -q 'zetaEulerHalfPower' DASHI/Crypto/MLKEMFIPS203F3329ArithmeticExact.agda
grep -q 'pair03DifferenceInverse' DASHI/Crypto/MLKEMFIPS203F3329ArithmeticExact.agda
grep -q 'transitionUncertaintyCost128' DASHI/Crypto/MLKEMUncertaintyTransitionCostBridgeExact.agda
grep -q 'pricedSearchEdgeUncertainty128' DASHI/Crypto/MLKEMProtectedLabelUncertaintyEdgeExact.agda
grep -q 'fullRankExactResidualTouchObstruction128' DASHI/Crypto/MLKEMExactResidualTouchLowerBoundExact.agda
grep -q 'sameOppositePairForcesSameParitySectors' DASHI/Crypto/MLKEMOppositeResidueParityFibreFactorisationExact.agda
grep -q 'sameParitySectorsForceSameOppositePair' DASHI/Crypto/MLKEMOppositeResidueParityFibreFactorisationExact.agda
grep -q 'oppositeResidueSumSelectsEven' DASHI/Crypto/MLKEMOppositeResidueParityDecompositionExact.agda
grep -q 'oppositeResidueDifferenceSelectsOdd' DASHI/Crypto/MLKEMOppositeResidueParityDecompositionExact.agda
grep -q 'twoRootsGiveLinearTimesQuadratic' DASHI/Crypto/MLKEMNTTPair03CubicRootFactorReductionExact.agda
grep -q 'pair03ReducedKernelCheckIsTrue' DASHI/Crypto/MLKEMNTTPair03ReducedKernelCertificateExact.agda
grep -q 'compactPair03BoundedKernelOnlyZero' DASHI/Crypto/MLKEMNTTPair03ReducedKernelCertificateExact.agda
grep -q 'pair01MassFromCollisionPairs' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q 'pair02MassFromCollisionPairs' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q 'pair03EnumerationHasNoCollisionPair' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q 'pair03EnumerationHasUnitMaxFibre' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q 'ObservationReflectsRawOnSecretImage' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q 'finiteCoarseningNotInjective' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q 'conditionedResidual0' DASHI/Crypto/MLKEMBaseCaseConditionedResidualExact.agda
grep -q 'conditionedResidual1' DASHI/Crypto/MLKEMBaseCaseConditionedResidualExact.agda
grep -q 'conditionedEquationLeavesTwoPlausibleSecrets' DASHI/Crypto/ConditionedResidualAmbiguityRegressionExact.agda
grep -q 'noUniqueMateFromConditioningAlone' DASHI/Crypto/ConditionalMateAmbiguityExact.agda
grep -q 'leftCandidateGivesGlobal' DASHI/Crypto/ConditionalReconciliationSearchExact.agda
grep -q 'actualCBD2SliceScalarCollision' DASHI/Crypto/MLKEMNTTActualCBD2ScalarCollisionExact.agda
grep -q 'nonCartesianCBD2NTTSlice' DASHI/Crypto/MLKEMNTTActualCBD2SliceCouplingExact.agda
grep -q 'twoScalarListSizeIs1' DASHI/Crypto/MLKEMNTTActualCBD2TwoScalarRefinementExact.agda
grep -q 'allTriplesCountIs125' DASHI/Crypto/MLKEMNTTActualCBD2FullTripleListProfileExact.agda
grep -q 'firstScalarHasExactly16CollisionPairs' DASHI/Crypto/MLKEMNTTActualCBD2FullTripleListProfileExact.agda
grep -q 'twoActualScalarsHaveNoCollisionPair' DASHI/Crypto/MLKEMNTTActualCBD2FullTripleListProfileExact.agda
grep -q 'firstScalarListMassIs157' DASHI/Crypto/MLKEMNTTActualCBD2ConditionalListMassExact.agda
grep -q 'jointTwoScalarListMassIs125' DASHI/Crypto/MLKEMNTTActualCBD2ConditionalListMassExact.agda
grep -q 'threshold0ListSize' DASHI/Crypto/FiniteMLWEListDecodingGeometryExact.agda
grep -q 'threshold2ListSize' DASHI/Crypto/FiniteMLWEListDecodingGeometryExact.agda
grep -q 'labConfirmationCost2NetGain' DASHI/Crypto/FiniteMLWEConfirmationObservationExact.agda
grep -q 'separatorObservationGain' DASHI/Crypto/ObservationSeparatorGeometryExact.agda
grep -q 'extendedLanguageSeparates' DASHI/Crypto/AttackerObservationLanguageRefinementExact.agda
grep -q 'minimaxWorstGain' DASHI/Crypto/RepresentationSecurityGameExact.agda
grep -q 'beneficialGeometryGain' DASHI/Crypto/ProtectedLabelSearchGeometryExact.agda
grep -q 'grayEmbeddingDistortionIs3' DASHI/Crypto/SearchGraphEmbeddingDistortionExact.agda
grep -q 'positivePathCostAtLeastEdgeCount' DASHI/Crypto/GrayPathTransitionOptimalExact.agda
grep -q 'grayAttainsPath4LowerBound' DASHI/Crypto/GrayPathTransitionOptimalExact.agda
grep -q 'grayPathCost' DASHI/Crypto/CBD2MixedRadixGrayTraversalExact.agda
grep -q 'lexExcessTransitionCost' DASHI/Crypto/CBD2MixedRadixGrayTraversalExact.agda
grep -q 'sameCandidatesSameRateDifferentTransitionCost' DASHI/Crypto/FiniteMLWETransitionGeometryExact.agda
grep -q 'grayTraversalSavesThreeWorkUnits' DASHI/Crypto/IncrementalResidualTraversalExact.agda
grep -q 'grayWeaklyDominatesBinary' DASHI/Crypto/CryptoRepresentationParetoExact.agda
grep -q 'observationShrinksResidualWidth' DASHI/Crypto/AdaptiveCandidateResidualWidthExact.agda
grep -q 'adaptiveSavesThreeBitMassUnits' DASHI/Crypto/ConditionalResidualRateExact.agda
grep -q 'statisticalGainDoesNotImplySearchGain' DASHI/Crypto/FiniteGuessingProbabilityExact.agda
grep -q 'sameLogicalTransitionDifferentPhysicalObservation' DASHI/Crypto/RepresentationLeakageGeometryExact.agda

grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMBaseCaseConditionedResidualExact.agda
grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMButterflyStageLocalityInvariantExact.agda
grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMOppositeResidueParityFibreFactorisationExact.agda
grep -q '10.6028/NIST.FIPS.203' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q '10.46586/tches.v2021.i4.88-113' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q '10.1007/978-3-031-54773-7_5' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q '10.46586/tches.v2025.i4.409-436' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q '10.1109/HOST55118.2023.10133270' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q '10.46586/tches.v2024.i3.200-223' DASHI/Crypto/MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact.agda
grep -q '10.1007/978-981-97-1235-9_11' DASHI/Crypto/MLKEMNTTActualCBD2ConditionalListMassExact.agda
grep -q 'ePrint 2023/1866' DASHI/Crypto/MLKEMUncertaintyTransitionCostBridgeExact.agda
grep -q '10.1016/j.disc.2021.112670' DASHI/Crypto/MLKEMFIPS203AverageSuccessResourceExact.agda

if command -v python3 >/dev/null 2>&1; then
  python3 scripts/crypto_ntt_pair03_compact_injectivity_certificate.py >/dev/null
  python3 scripts/crypto_ntt_cbd_block_reconciliation_probe.py \
    --trials 2 --max-block 8 --baseline-pairs 2 >/dev/null
  python3 scripts/crypto_ntt_opposite_residue_factorized_membership.py \
    --m 8 --trials 2 >/dev/null
else
  echo "python3 unavailable: skipped Round-17 discovery regressions" >&2
fi

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/Crypto/BlueTeamSearchObservationRound17.agda
else
  echo "agda unavailable: structural/fail-closed + Python Round-17 scans completed; no kernel-clean claim"
fi
