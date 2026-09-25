#!/usr/bin/env bash
set -euo pipefail

targets=(
  DASHI/Moonshine/JInvariant369C6TenRankWeightTwelveCrossPollinationExact.agda
  DASHI/Moonshine/JInvariant369CanonicalInterpretationExact.agda
  DASHI/Moonshine/MonsterAtlas6561X8RecognitionObligationExact.agda
  DASHI/Moonshine/JInvariant369NeutralCuspRelationCrossPollinationExact.agda
  DASHI/Moonshine/JInvariant369SSP15SignedFRACTRANBranchExact.agda
  DASHI/Moonshine/JInvariant369OggAddressSSP15NoGoExact.agda
  DASHI/Moonshine/JInvariant369SSP15PrimeInternalFibreExact.agda
  DASHI/Moonshine/OggSSPSmallCharacteristicResidualCodecExact.agda
  DASHI/Moonshine/OggSSPSmallCharacteristicCodecIndexedRecognitionExact.agda
  DASHI/Moonshine/OggSSP369RecognitionFunctorObligationExact.agda
  DASHI/Moonshine/OggSSPCoarseSupersingularJRecognitionNoGoExact.agda
  DASHI/Moonshine/OggSSPP3F9FrobeniusCandidateNoGoExact.agda
  DASHI/Moonshine/OggSSPSmallCharacteristicArithmeticSourceSocketExact.agda
  DASHI/Moonshine/OggSSPArithmeticTo369RecognitionExact.agda
)

for target in "${targets[@]}"; do
  test -f "$target"
done

grep -q 'smithHalfTurnCommutesWithModularReflection' "${targets[0]}"
grep -q 'rank14IsRank13PlusOne' "${targets[0]}"
grep -q 'twelveSquaredIs144' "${targets[0]}"
grep -q 'twelveCubedIs1728' "${targets[0]}"
grep -q 'signedMagnitudeStillCannotFactorThroughCoarseLevel3' "${targets[0]}"
grep -q 'signedMagnitudeDoesNotFactorThroughLevel3' "${targets[1]}"
grep -q 'NineBy729BlockRecognition' "${targets[2]}"
grep -q 'Atlas6561X8Recognition' "${targets[2]}"
grep -q 'x8EquivariantRecognitionInhabitedHere' "${targets[2]}"
grep -q 'innerNineToFiveOrbitQuotientIsPaid' "${targets[3]}"
grep -q 'phasePreservingThreeTimesFiveReductionIsPaid' "${targets[3]}"
grep -q 'joinAfterSplit' "${targets[3]}"
grep -q 'distinguishedOrientationDuplicationCollapses' "${targets[3]}"
grep -q 'fourteenIsBalancedRankCarry' "${targets[3]}"
grep -q 'leanEta24NormalizedDeltaSameObjectSourceWritten' "${targets[3]}"
grep -q 'twelvePlusTwelveIsTwentyFour' "${targets[3]}"
grep -q 'finiteZeroPhaseDoesNotEqualCuspVanishing' "${targets[3]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"

grep -q 'chosenOggInternalLaneBijection' "${targets[4]}"
grep -q 'lanePrimeToSignedPrime' "${targets[4]}"
grep -q 'internalPointedCoarseRoundTrip' "${targets[4]}"
grep -q 'neutralValuationIsZeroAt' "${targets[4]}"
grep -q 'zeroValuationCannotRecoverSelectedNeutralLane' "${targets[4]}"
grep -q 'executeSeedProgram' "${targets[4]}"

grep -q 'p2AndP11HaveSameAddressCoarse10' "${targets[5]}"
grep -q 'addressModeNever09' "${targets[5]}"
grep -q 'modePreservingOggInternalBijectionImpossible' "${targets[5]}"
grep -q 'chosenCarrierBijectionDerivedFromAddressLaw' "${targets[5]}"

grep -q 'primeInternalCountArithmetic' "${targets[6]}"
grep -q 'chosenGaugeAtP71IsNotNeutral' "${targets[6]}"
grep -q 'everyPrimeHasEveryInternalLane' "${targets[6]}"
grep -q 'chosenGaugeExhaustsSemanticCarrier' "${targets[6]}"

grep -q 'primeInternalToPointedSigned' "${targets[6]}"
grep -q 'primeInternalValuationOwnLane' "${targets[6]}"
grep -q 'canonicalSignedLiftUsesPrimeInternalPair' "${targets[6]}"


grep -q 'p2CoarseProjectionHasNoLeftInverse' "${targets[7]}"
grep -q 'p3CoarseProjectionHasNoLeftInverse' "${targets[7]}"
grep -q 'exactLaneKeyAddressDeterminesLane' "${targets[8]}"
grep -q 'p2RecognitionLaneKey' "${targets[9]}"
grep -q 'p2FiveOrbitProjectionCannotReopenTenCarrier' "${targets[9]}"


grep -q 'noCoarseJPi0SurjectionToP3' "${targets[10]}"
grep -q 'noCoarseJPi0SurjectionToP2Retained' "${targets[10]}"
grep -q 'noInjectiveF9OrbitToP3Target' "${targets[11]}"
grep -q 'noFullF9FrobeniusRecognitionToP3' "${targets[11]}"

grep -q 'p3ReceiptFrobeniusOrderTwo' "${targets[12]}"
grep -q 'P3MarkedFrobeniusSource' "${targets[12]}"
grep -q 'P2MarkedArithmeticSource' "${targets[12]}"
grep -q 'wholeF9FrobeniusCarrierRejected' "${targets[12]}"

grep -q 'P3ArithmeticTo369Recognition' "${targets[13]}"
grep -q 'P2ArithmeticTo369Recognition' "${targets[13]}"
grep -q 'reverseCompatibilityDoesNotBuildArithmeticTo369' "${targets[13]}"
