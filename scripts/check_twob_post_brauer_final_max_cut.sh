#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Moonshine/OggSSP2BTate276M24BrauerRuntimeReceiptExact.agda
  DASHI/Moonshine/OggSSP2BDefectTwoBitProvenanceSelectorExact.agda
  DASHI/Moonshine/OggSSP2BDefectProvenanceSearchNoGoExact.agda
  DASHI/Moonshine/OggSSP2BMonster2LocalThree276SourceExact.agda
  DASHI/Moonshine/OggSSP2BFi22d2NaturalTenSourceExact.agda
  DASHI/Moonshine/OggSSP2BMonsterGF2RepresentationSourceExact.agda
  DASHI/Moonshine/OggSSP2BPostBrauerOuterActionBlindSpotExact.agda
  DASHI/Moonshine/OggSSP2BSemisimplificationSelfDualityExtensionNoGoExact.agda
  DASHI/Moonshine/OggSSP2BIteratedTateDefectTargetExact.agda
  DASHI/Moonshine/OggSSP2BM22d2OuterClassDuadDefectExact.agda
  DASHI/Moonshine/OggSSP2BWeightTwoIntegralC2DecompositionExact.agda
  DASHI/Moonshine/OggSSP2BTatePlusMinusCokernelExact.agda
  DASHI/Moonshine/OggSSP2BCo1UntwistedSectorSplitExact.agda
  DASHI/Moonshine/OggSSP2BCo1ExteriorSquareTateCandidateExact.agda
  DASHI/Moonshine/OggSSP2BCo1AugmentationTrivialityCriterionExact.agda
  DASHI/Moonshine/OggSSP2BCo1FrobeniusHomRigidityExact.agda
  DASHI/Moonshine/OggSSP2BCentralizerMod2CancellationRigidityExact.agda
  DASHI/Moonshine/OggSSP2BTateCokernelRankRigidityExact.agda
  DASHI/Moonshine/OggSSP2BPostBrauerSameObjectFrontierExact.agda
  DASHI/Moonshine/OggSSP2BCompletionAcquisitionFrontierExact.agda
)

for target in "${targets[@]}"; do
  test -f "$target"
done

grep -q 'allBrauerRowsMatchIsTrue' "${targets[0]}"
grep -q 'semisimplifiedIngressIsPaid' "${targets[0]}"
grep -q 'literalModuleIsomorphismStillOpen' "${targets[0]}"
grep -q 'explicitQ10StillOpen' "${targets[0]}"

grep -q 'provenanceChoiceCountIsFour' "${targets[1]}"
grep -q 'orderFourIsForced' "${targets[1]}"

grep -q 'remainingSourceDecisionCountIsTwo' "${targets[2]}"
grep -q 'orientedRouteDoesNotSourceSelectBits' "${targets[2]}"
grep -q 'galoisRouteDoesNotSourceSelectBits' "${targets[2]}"

grep -q 'three276SourcePaid' "${targets[3]}"
grep -q 'characteristicTwoTateIdentificationStillOpen' "${targets[3]}"

grep -q 'normalKernelRankIsTen' "${targets[4]}"
grep -q 'fi22NaturalTenDoesNotIdentifyActualTateQ10' "${targets[4]}"

grep -q 'monsterGF2DimensionExact' "${targets[5]}"
grep -q 'existenceDoesNotConstructStableQ10' "${targets[5]}"

grep -q 'brauerPassDoesNotDetermineOuterJ2x5Action' "${targets[6]}"

grep -q 'sameSemisimplifiedProfile' "${targets[7]}"
grep -q 'fixedCountsDiffer' "${targets[7]}"

grep -q 'completion10IteratedTateDefectIsZero' "${targets[8]}"

grep -q 'duadRankIs132' "${targets[9]}"
grep -q 'duadFixedDimensionIs144' "${targets[9]}"
grep -q 'duadIteratedTateDefectIs12' "${targets[9]}"

grep -q 'integralRankClosure' "${targets[10]}"
grep -q 'plusEigenspaceIs98580' "${targets[10]}"

grep -q 'dimensionClosure' "${targets[11]}"
grep -q 'candidateSym2QuotientIs276' "${targets[11]}"

grep -q 'untwistedPlusDimensionIs98580' "${targets[12]}"
grep -q 'actualNormImagePlacementStillOpen' "${targets[12]}"

grep -q 'sameObjectExteriorSquareStillOpen' "${targets[13]}"

grep -q 'canonicalPromotionBoundary' "${targets[14]}"

grep -q 'exteriorQuotientDimensionIs276' "${targets[15]}"
grep -q 'common98280MapStillOpen' "${targets[15]}"

grep -q 'commonPlusResidualIsMinus' "${targets[16]}"
grep -q 'actualNormCommon98280StillOpen' "${targets[16]}"

grep -q 'rankRigidityClosure' "${targets[17]}"
grep -q 'forcedRankNullityClosure' "${targets[17]}"

grep -q 'brauerAllRowsMatch' "${targets[18]}"
grep -q 'actualOuterActionOnSameQStillOpen' "${targets[18]}"

grep -q 'canonicalCompletionAcquisitionStatus' "${targets[19]}"
grep -q 'integralWeightTwoRankClosurePaid' "${targets[19]}"
grep -q 'frobeniusExteriorQuotientDimensionIs276' "${targets[19]}"
grep -q 'actualNormCommon98280StillOpen' "${targets[19]}"
grep -q 'remainingDefectSourceBitsIsTwo' "${targets[19]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
