#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ "${POINTED_BULK_SKIP_BASE:-0}" != "1" ]]; then
  bash scripts/check_conscious_access_round5.sh
  CABARLAH_SKIP_ROUND5=1 bash scripts/check_cabarlah_palestine_formalism.sh
fi

FILES=(
  DASHI/Core/Optional.agda
  DASHI/Biology/PointedTernaryBulkExact.agda
  DASHI/Biology/DecimalTenTernaryPresentationExact.agda
  DASHI/Biology/ThreeSixNineMoonshineScaleExact.agda
  DASHI/Biology/ReducedFiftyThreeOrbitCandidateExact.agda
  DASHI/Biology/SporadicSignedFiftyThreeTarotProjectionExact.agda
  DASHI/Biology/SporadicTarotDependencyExact.agda
  DASHI/Biology/TarotCarrierExact.agda
  DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
  DASHI/Biology/JMDSporadicTarotV2Regression.agda
  DASHI/Biology/JMDSporadicTarotOrdinalTotalisationExact.agda
  DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
  DASHI/Biology/StageSymmetrySSP15SpectrumExact.agda
  DASHI/Biology/ImageHexagramSSP15MDLExact.agda
  DASHI/Biology/SporadicStageSymmetryTarotRegression.agda
  DASHI/Biology/PointedBulkReducedMoonshineBoundary.agda
  DASHI/Biology/PointedBulkSporadicTarotSourceAtlas.agda
  DASHI/Biology/PointedBulkSporadicTarotEverything.agda
  DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
  DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
  DASHI/Foundations/BalancedTernaryUltrametricExact.agda
  DASHI/Foundations/StageSymmetryCarrierTowerExact.agda
  DASHI/Foundations/CounterpositionOrderedJoinExact.agda
  DASHI/Foundations/DialecticSheetFrameSelectorExact.agda
  DASHI/Foundations/FrameWitnessFibreMDLExact.agda
  DASHI/Foundations/DialecticCubieTetralemmaExact.agda
  DASHI/Foundations/SecondRevolutionJankoTarotExact.agda
  DASHI/Moonshine/DepthTwoNonaryResidueFibreExact.agda
  DASHI/Moonshine/EulerMonsterMeaningSeparationExact.agda
  DASHI/Governance/CabarlahTraumaProjectionBridgeExact.agda
  DASHI/Governance/Everything.agda
  DASHI/PointedBulkSporadicTarotCabarlahBoundary.agda
  DASHI/PointedBulkSporadicTarotCabarlahRegression.agda
  DASHI/EverythingPointedBulkSporadicTarot.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'optionalMapIdentity' DASHI/Core/Optional.agda
grep -q 'open import DASHI.Core.Optional public' DASHI/Biology/SporadicTarotDependencyExact.agda
grep -q 'open import DASHI.Core.Optional public' DASHI/Foundations/DialecticSheetFrameSelectorExact.agda
grep -q 'open import DASHI.Core.Optional public' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'pointedBulkDimensionIs196830' DASHI/Biology/PointedTernaryBulkExact.agda
grep -q 'candidateR53DimensionIsFiftyThree' DASHI/Biology/ReducedFiftyThreeOrbitCandidateExact.agda
grep -q 'sporadicInventoryCountIsTwentySix' DASHI/Biology/SporadicTarotDependencyExact.agda
grep -q 'majorArcanaCountIsTwentyTwo' DASHI/Biology/TarotCarrierExact.agda

# JMD poster transcription and non-promotion guards.
grep -q 'jmdV2Assignment Sporadic.M11' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'jmdV2Assignment Sporadic.Fi22' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'co4StrengthAssignment' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'posterSuppliesTotalS26ToA22MapIsFalse' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda

# Balanced ternary, signed amplitude, full Stage-5 branching, and ultrametric.
grep -q 'stage5To3RetainsTwo' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'residualErasedIsFalse' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'allOpenPatternHasS3' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'counterpositionPatternHasS2' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'decodedWeightsExact' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'prefixDepthExact' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'independentEvidenceForTenTimesThreePowerNineIsFalse' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'triadAmplitude' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'joinedAmplitudeRangeConstructedIsTrue' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'closesAtNext3 : value + deficit3 ≡ 3 \* (suc quotient3)' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'fiveResidueDeficitProfile' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'positiveStageFiveCompletion' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'negativeStageFiveResolution' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'negativeBranchRetainsS2' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'stageFiveFallbackWithResidual' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'irrepDecompositionGeneratesPrimaryFiveToThreeArithmeticIsFalse' DASHI/Foundations/BalancedTernaryAmplitudeClosureExact.agda
grep -q 'prefixAgreementTransitive' DASHI/Foundations/BalancedTernaryUltrametricExact.agda
grep -q 'prefixAgreementReflexive' DASHI/Foundations/BalancedTernaryUltrametricExact.agda
grep -q 'prefixAgreementWeaken' DASHI/Foundations/BalancedTernaryUltrametricExact.agda
grep -q 'fiveSixAgreeThroughDepthTwo' DASHI/Foundations/BalancedTernaryUltrametricExact.agda
grep -q 'constituentSuffixesErasedIsFalse' DASHI/Foundations/BalancedTernaryUltrametricExact.agda
grep -q 'hexadicCardinalityIsSix' DASHI/Foundations/StageSymmetryCarrierTowerExact.agda
grep -q 'squareEnumerationMatchesCardinality' DASHI/Foundations/StageSymmetryCarrierTowerExact.agda
grep -q 'hexadicEnumerationMatchesCardinality' DASHI/Foundations/StageSymmetryCarrierTowerExact.agda
grep -q 'nonaryEnumerationMatchesCardinality' DASHI/Foundations/StageSymmetryCarrierTowerExact.agda
grep -q 'totalAmplitudeFromConstituents' DASHI/Foundations/StageSymmetryCarrierTowerExact.agda

# Binary embedding, context counterpositions, ordered joins, and square actions.
grep -q 'binaryEmbeddingInjective' DASHI/Foundations/CounterpositionOrderedJoinExact.agda
grep -q 'binaryEmbeddingNeverNeutral' DASHI/Foundations/CounterpositionOrderedJoinExact.agda
grep -q 'partialCounterpositionIsNotFullInverse' DASHI/Foundations/CounterpositionOrderedJoinExact.agda
grep -q 'orderedStageFiveJoinsShareAmplitude' DASHI/Foundations/CounterpositionOrderedJoinExact.agda
grep -q 'orderedStageFiveJoinsDiffer' DASHI/Foundations/CounterpositionOrderedJoinExact.agda
grep -q 'squareMoveCountIsEight' DASHI/Foundations/CounterpositionOrderedJoinExact.agda
grep -q 'squareStateCarrierIdentifiedWithSquareMoveCarrierIsFalse' DASHI/Foundations/CounterpositionOrderedJoinExact.agda
! grep -q 'counterUnder .* pattern' DASHI/Foundations/CounterpositionOrderedJoinExact.agda

# Image/hexagram/frame selector, witness fibre, finite MDL, and cubie layers.
grep -q 'selectInhabitableFrame' DASHI/Foundations/DialecticSheetFrameSelectorExact.agda
grep -q 'counterFrameFailsSynthesis' DASHI/Foundations/DialecticSheetFrameSelectorExact.agda
grep -q 'localWitnessImpliesUniversalTruthIsFalse' DASHI/Foundations/DialecticSheetFrameSelectorExact.agda
grep -q 'allAdmissibleWitnesses' DASHI/Foundations/FrameWitnessFibreMDLExact.agda
grep -q 'canonicalFrameMDLSelection' DASHI/Foundations/FrameWitnessFibreMDLExact.agda
grep -q 'finiteMDLMinimiserConstructedIsTrue' DASHI/Foundations/FrameWitnessFibreMDLExact.agda
grep -q 'lowestCostFrameIsUniversallyTrueIsFalse' DASHI/Foundations/FrameWitnessFibreMDLExact.agda
grep -q 'stageThreeCarrierRetained' DASHI/Foundations/DialecticCubieTetralemmaExact.agda
grep -q 'cubiePositionCardinalityIsTwentySeven' DASHI/Foundations/DialecticCubieTetralemmaExact.agda
grep -q 'decisionPoliciesDifferOnNegative' DASHI/Foundations/DialecticCubieTetralemmaExact.agda
grep -q 'cubieListAloneProvesManifoldIsFalse' DASHI/Foundations/DialecticCubieTetralemmaExact.agda
grep -q 'pipelineHasSevenTypedStages' DASHI/Biology/ImageHexagramSSP15MDLExact.agda
grep -q 'resolutionPredictedIsFalse' DASHI/Biology/ImageHexagramSSP15MDLExact.agda
grep -q 'scalarTraceReconstructsHeisenbergGeometryIsFalse' DASHI/Biology/ImageHexagramSSP15MDLExact.agda
! grep -q 'swapFirstSecond pattern' DASHI/Biology/ImageHexagramSSP15MDLExact.agda

# Reused and enriched SSP15/Ogg lane infrastructure.
grep -q 'allOggPrimeLanes = Lane.canonicalMonsterPrimeLane' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
grep -q 'oggPrimeLaneCountIsFifteen' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
grep -q 'oggLaneCountWitness' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
grep -q 'existingPrimeInfrastructureReusedIsTrue' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
grep -q 'arithmetic71ConstructsInvariantComplementIsFalse' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
grep -q 'RichSSP15Signature' DASHI/Biology/StageSymmetrySSP15SpectrumExact.agda
grep -q 'signaturesDifferAtP71' DASHI/Biology/StageSymmetrySSP15SpectrumExact.agda
grep -q 'everyOrderPMonsterClassHasSameGamma0PlusHauptmodulIsFalse' DASHI/Biology/StageSymmetrySSP15SpectrumExact.agda
grep -q 'divinationSemanticsEstablishedByMoonshineSourcesIsFalse' DASHI/Biology/StageSymmetrySSP15SpectrumExact.agda

# Exact depth-two nonary arithmetic, complete equivalence obligation, and tetration boundary.
grep -q 'moonshineCoefficientTernaryExpansion' DASHI/Moonshine/DepthTwoNonaryResidueFibreExact.agda
grep -q 'canonicalDepthTwoCommutingSquare' DASHI/Moonshine/DepthTwoNonaryResidueFibreExact.agda
grep -q 'terminalProductCountIsFiftyFour' DASHI/Moonshine/DepthTwoNonaryResidueFibreExact.agda
grep -q 'distinguishedOnly' DASHI/Moonshine/DepthTwoNonaryResidueFibreExact.agda
grep -q 'decodeEncode' DASHI/Moonshine/DepthTwoNonaryResidueFibreExact.agda
grep -q 'literalNineTetrationLevelTwo' DASHI/Moonshine/DepthTwoNonaryResidueFibreExact.agda
grep -q 'canonicalEightyOneBlockMonsterModuleDecompositionIsFalse' DASHI/Moonshine/DepthTwoNonaryResidueFibreExact.agda
grep -q 'modEightyOneIsIndependentEvidenceForSelectedChartIsFalse' DASHI/Moonshine/DepthTwoNonaryResidueFibreExact.agda

# Actual total map and signed 53 -> 22 observer.
grep -q 'familyCompressionTotalisation' DASHI/Biology/JMDSporadicTarotOrdinalTotalisationExact.agda
grep -q 'fi23BabyMonsterCollision' DASHI/Biology/JMDSporadicTarotOrdinalTotalisationExact.agda
grep -q 'totalMapIsSourceForcedIsFalse' DASHI/Biology/JMDSporadicTarotOrdinalTotalisationExact.agda
grep -q 'sporadicSignedDimensionIsFiftyThree' DASHI/Biology/SporadicSignedFiftyThreeTarotProjectionExact.agda
grep -q 'polaritiesShareArcana' DASHI/Biology/SporadicSignedFiftyThreeTarotProjectionExact.agda
grep -q 'completeHebrewLetterAssignmentSuppliedIsFalse' DASHI/Biology/SporadicSignedFiftyThreeTarotProjectionExact.agda
grep -q 'actualReducedMode53EquivalenceConstructedIsFalse' DASHI/Biology/SporadicSignedFiftyThreeTarotProjectionExact.agda
grep -q 'tarotProjectionIsGroupTheoreticQuotientIsFalse' DASHI/Biology/SporadicSignedFiftyThreeTarotProjectionExact.agda

# Dual second-revolution and Euler/Monster meaning separation.
grep -q 'carryOffsetExact' DASHI/Foundations/SecondRevolutionJankoTarotExact.agda
grep -q 'globalIsTenPlusLocalOffset' DASHI/Foundations/SecondRevolutionJankoTarotExact.agda
grep -q 'stageCarrierIdentifiedWithJankoGroupIsFalse' DASHI/Foundations/SecondRevolutionJankoTarotExact.agda
grep -q 'oneTwoOneFiniteEulerCharacteristicVanishes' DASHI/Moonshine/EulerMonsterMeaningSeparationExact.agda
grep -q 'oneTwoOneSupertraceVanishes' DASHI/Moonshine/EulerMonsterMeaningSeparationExact.agda
grep -q 'differentialSquaresToZero' DASHI/Moonshine/EulerMonsterMeaningSeparationExact.agda
grep -q 'coefficient196884IsEulerCharacteristicClaimedIsFalse' DASHI/Moonshine/EulerMonsterMeaningSeparationExact.agda

echo "Pointed bulk / sporadic Tarot / amplitude / counterposition / SSP15 / depth-two static guards passed."

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/JMDSporadicTarotV2Regression.agda \
  DASHI/Biology/SporadicStageSymmetryTarotRegression.agda \
  DASHI/PointedBulkSporadicTarotCabarlahRegression.agda \
  DASHI/PointedBulkSporadicTarotCabarlahBoundary.agda \
  DASHI/EverythingPointedBulkSporadicTarot.agda
