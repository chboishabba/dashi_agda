#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ "${POINTED_BULK_SKIP_BASE:-0}" != "1" ]]; then
  bash scripts/check_conscious_access_round5.sh
  CABARLAH_SKIP_ROUND5=1 bash scripts/check_cabarlah_palestine_formalism.sh
fi

FILES=(
  DASHI/Biology/PointedTernaryBulkExact.agda
  DASHI/Biology/DecimalTenTernaryPresentationExact.agda
  DASHI/Biology/ThreeSixNineMoonshineScaleExact.agda
  DASHI/Biology/ReducedFiftyThreeOrbitCandidateExact.agda
  DASHI/Biology/SporadicTarotDependencyExact.agda
  DASHI/Biology/TarotCarrierExact.agda
  DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
  DASHI/Biology/JMDSporadicTarotV2Regression.agda
  DASHI/Biology/JMDSporadicTarotOrdinalTotalisationExact.agda
  DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
  DASHI/Biology/SporadicStageSymmetryTarotRegression.agda
  DASHI/Biology/PointedBulkReducedMoonshineBoundary.agda
  DASHI/Biology/PointedBulkSporadicTarotSourceAtlas.agda
  DASHI/Biology/PointedBulkSporadicTarotEverything.agda
  DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
  DASHI/Foundations/BalancedTernaryUltrametricExact.agda
  DASHI/Foundations/StageSymmetryCarrierTowerExact.agda
  DASHI/Foundations/DialecticSheetFrameSelectorExact.agda
  DASHI/Foundations/SecondRevolutionJankoTarotExact.agda
  DASHI/Moonshine/EulerMonsterMeaningSeparationExact.agda
  DASHI/Governance/CabarlahTraumaProjectionBridgeExact.agda
  DASHI/Governance/Everything.agda
  DASHI/PointedBulkSporadicTarotCabarlahBoundary.agda
  DASHI/PointedBulkSporadicTarotCabarlahRegression.agda
  DASHI/EverythingPointedBulkSporadicTarot.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required pointed-bulk/sporadic-Tarot source is missing: $file" >&2
    exit 1
  fi

  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'pointedBulkDimensionIs196830' DASHI/Biology/PointedTernaryBulkExact.agda
grep -q 'candidateR53DimensionIsFiftyThree' DASHI/Biology/ReducedFiftyThreeOrbitCandidateExact.agda
grep -q 'sporadicInventoryCountIsTwentySix' DASHI/Biology/SporadicTarotDependencyExact.agda
grep -q 'majorArcanaCountIsTwentyTwo' DASHI/Biology/TarotCarrierExact.agda

# JMD poster transcription and non-promotion guards.
grep -q 'jmdV2Assignment Sporadic.M11' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'jmdV2Assignment Sporadic.Fi22' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'co4StrengthAssignment' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'actualInventoryAccounting' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'posterCardCountIsTwentyTwo' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'posterSuppliesTotalS26ToA22MapIsFalse' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda
grep -q 'omittedGroupsMayBeAssignedWithoutRationaleIsFalse' DASHI/Biology/JMDSporadicTarotV2CorrespondenceExact.agda

# Balanced ternary, retained fallback, ultrametric prefix, and symmetry.
grep -q 'stage5To3RetainsTwo' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'residualErasedIsFalse' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'counterpositionNeedNotBeInverse' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'eightyOneSplitsTenAndSeventyOne' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'independentEvidenceForTenTimesThreePowerNineIsFalse' DASHI/Foundations/BalancedTernaryStageSymmetryExact.agda
grep -q 'prefixAgreementTransitive' DASHI/Foundations/BalancedTernaryUltrametricExact.agda
grep -q 'fiveSixAgreeThroughDepthTwo' DASHI/Foundations/BalancedTernaryUltrametricExact.agda
grep -q 'constituentSuffixesErasedIsFalse' DASHI/Foundations/BalancedTernaryUltrametricExact.agda
grep -q 'hexadicCardinalityIsSix' DASHI/Foundations/StageSymmetryCarrierTowerExact.agda
grep -q 'nonaryCardinalityIsNine' DASHI/Foundations/StageSymmetryCarrierTowerExact.agda

# Image/hexagram selector witness boundary.
grep -q 'selectInhabitableFrame' DASHI/Foundations/DialecticSheetFrameSelectorExact.agda
grep -q 'localWitnessImpliesUniversalTruthIsFalse' DASHI/Foundations/DialecticSheetFrameSelectorExact.agda

# Reused SSP15/Ogg lane infrastructure.
grep -q 'allOggPrimeLanes = Lane.canonicalMonsterPrimeLane' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
grep -q 'SSP15Signature' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
grep -q 'oggPrimeLaneCountIsFifteen' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
grep -q 'existingPrimeInfrastructureReusedIsTrue' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
grep -q 'arithmetic71ConstructsInvariantComplementIsFalse' DASHI/Biology/StageSymmetrySSP15BridgeExact.agda

# Actual total map with explicit collisions and authority.
grep -q 'familyCompressionTotalisation' DASHI/Biology/JMDSporadicTarotOrdinalTotalisationExact.agda
grep -q 'fi23BabyMonsterCollision' DASHI/Biology/JMDSporadicTarotOrdinalTotalisationExact.agda
grep -q 'totalMapIsSourceForcedIsFalse' DASHI/Biology/JMDSporadicTarotOrdinalTotalisationExact.agda
grep -q 'symbolicRationalesPromotedToGroupTheoremsIsFalse' DASHI/Biology/JMDSporadicTarotOrdinalTotalisationExact.agda

# Dual second-revolution and Euler/Monster meaning separation.
grep -q 'address14' DASHI/Foundations/SecondRevolutionJankoTarotExact.agda
grep -q 'stageCarrierIdentifiedWithJankoGroupIsFalse' DASHI/Foundations/SecondRevolutionJankoTarotExact.agda
grep -q 'differentialSquaresToZero' DASHI/Moonshine/EulerMonsterMeaningSeparationExact.agda
grep -q 'coefficient196884IsEulerCharacteristicClaimedIsFalse' DASHI/Moonshine/EulerMonsterMeaningSeparationExact.agda

echo "Pointed bulk / sporadic Tarot / balanced-stage symmetry static guards passed."

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/JMDSporadicTarotV2Regression.agda \
  DASHI/Biology/SporadicStageSymmetryTarotRegression.agda \
  DASHI/PointedBulkSporadicTarotCabarlahRegression.agda \
  DASHI/PointedBulkSporadicTarotCabarlahBoundary.agda \
  DASHI/EverythingPointedBulkSporadicTarot.agda
