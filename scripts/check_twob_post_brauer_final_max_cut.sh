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
grep -q 'defectProfileDoesNotConstructTwoProvenanceBits' "${targets[1]}"

grep -q 'remainingSourceDecisionCountIsTwo' "${targets[2]}"
grep -q 'orientedRouteDoesNotSourceSelectBits' "${targets[2]}"
grep -q 'galoisRouteDoesNotSourceSelectBits' "${targets[2]}"
grep -q 'provenanceChoiceCountStillFour' "${targets[2]}"

grep -q 'three276SourcePaid' "${targets[3]}"
grep -q 'trialitySourcePaid' "${targets[3]}"
grep -q 'characteristicTwoTateIdentificationStillOpen' "${targets[3]}"

grep -q 'normalKernelRankIsTen' "${targets[4]}"
grep -q 'fi22NaturalTenDoesNotIdentifyActualTateQ10' "${targets[4]}"
grep -q 'runtimeOuterJ2x5OnNaturalTenPaid' "${targets[4]}"

grep -q 'monsterGF2DimensionExact' "${targets[5]}"
grep -q 'explicitMonsterGF2RepresentationSourced' "${targets[5]}"
grep -q 'existenceDoesNotConstructStableQ10' "${targets[5]}"

grep -q 'brauerIngressPaid' "${targets[6]}"
grep -q 'finiteOuterSourceFound' "${targets[6]}"
grep -q 'brauerPassDoesNotDetermineOuterJ2x5Action' "${targets[6]}"

grep -q 'sameSemisimplifiedProfile' "${targets[7]}"
grep -q 'nonsplitPreservesForm' "${targets[7]}"
grep -q 'fixedCountsDiffer' "${targets[7]}"
grep -q 'semisimplificationAndSelfDualityDetermineExtension' "${targets[7]}"

grep -q 'completion10IteratedTateDefectIsZero' "${targets[8]}"
grep -q 'duadOuterClassRuntimeScreenImplemented' "${targets[8]}"
grep -q 'actualTwoBKleinFourIteratedTateComputed' "${targets[8]}"

grep -q 'm24TwoBCentralizerIsTwelveTimesLocal' "${targets[9]}"
grep -q 'duadRankIs132' "${targets[9]}"
grep -q 'duadFixedDimensionIs144' "${targets[9]}"
grep -q 'duadIteratedTateDefectIs12' "${targets[9]}"

grep -q 'brauerAllRowsMatch' "${targets[10]}"
grep -q 'semisimplifiedIngressIsPaid' "${targets[10]}"
grep -q 'outerJ2x5MatchesTwo' "${targets[10]}"
grep -q 'remainingDefectSourceDecisionCountIsTwo' "${targets[10]}"
grep -q 'nineOrbitIndexingIsNotSemanticIdentity' "${targets[10]}"
grep -q 'actualOuterActionOnSameQStillOpen' "${targets[10]}"

grep -q 'canonicalCompletionAcquisitionStatus' "${targets[11]}"
grep -q 'postBrauerSemisimplifiedIngressAlreadyPaid' "${targets[11]}"
grep -q 'fi22NaturalTenRankIsTen' "${targets[11]}"
grep -q 'monsterGF2DimensionIs196882' "${targets[11]}"
grep -q 'remainingDefectSourceBitsIsTwo' "${targets[11]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
