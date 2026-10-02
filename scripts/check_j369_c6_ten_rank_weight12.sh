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
  DASHI/Moonshine/OggP31CompletionTenTwoSevenNineCrossPollinationExact.agda
  DASHI/Moonshine/TwoSevenNineNumberRoleHubExact.agda
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
grep -q 'extensionCoordinateEquivariant' "${targets[11]}"
grep -q 'f9ExtensionCoordinateNotPi0Embedding' "${targets[11]}"
grep -q 'noFullF9FrobeniusRecognitionToP3' "${targets[11]}"

grep -q 'p3ReceiptFrobeniusOrderTwo' "${targets[12]}"
grep -q 'P3MarkedFrobeniusSource' "${targets[12]}"
grep -q 'P2MarkedArithmeticSource' "${targets[12]}"
grep -q 'wholeF9FrobeniusCarrierRejected' "${targets[12]}"

grep -q 'P3ArithmeticTo369Recognition' "${targets[13]}"
grep -q 'P2ArithmeticTo369Recognition' "${targets[13]}"
grep -q 'reverseCompatibilityDoesNotBuildArithmeticTo369' "${targets[13]}"

grep -q 'completionTenTo279TypedComposite' "${targets[14]}"
grep -q 'pointedThirtyIsP31' "${targets[14]}"
grep -q 'nonaryPointedP31Is279' "${targets[14]}"
grep -q 'p31IsCanonicalRankTen' "${targets[14]}"
grep -q 'twoDistinct276RolesNotIdentifiedHere' "${targets[14]}"
grep -q 'moonshineObserver279Is279' "${targets[15]}"
grep -q 'principiaCardinalKeyword279Is279' "${targets[15]}"
grep -q 'sameScalarDoesNotIdentifyRoles' "${targets[15]}"


# Generic exceptional-residual target family + arithmetic acquisition wall.
residual_targets=(
  DASHI/Foundations/BalancedTernaryHypercubeAntipodalOrbitCountExact.agda
  DASHI/Moonshine/OggSSPExponentResidualArithmeticSourceInterfaceExact.agda
  DASHI/Moonshine/OggSSPExponentResidualVsSupersingularOrbitSeparationExact.agda
)

for target in "${residual_targets[@]}"; do
  test -f "$target"
done

scripts/run_agda29_parallel_check.sh "${residual_targets[@]}"

grep -q 'ternaryStateSplitExact' "${residual_targets[0]}"
grep -q 'doubleOrbitCountExact' "${residual_targets[0]}"
grep -q 'orbitCountOneIsTwo' "${residual_targets[0]}"
grep -q 'orbitCountTwoIsFive' "${residual_targets[0]}"
grep -q 'orbitCountThreeIsFourteen' "${residual_targets[0]}"
grep -q 'p2RetainedBinarySheetCount' "${residual_targets[0]}"

grep -q 'p3TargetPi0IsOneTritAntipodalOrbitCount' "${residual_targets[1]}"
grep -q 'p2TargetPi0IsRetainedBinaryOverTwoTritOrbitCount' "${residual_targets[1]}"
grep -q 'hypercubeTargetCountDoesNotConstructArithmeticResidualSource' "${residual_targets[1]}"
grep -q 'ResidualPresentationSameObject' "${residual_targets[1]}"

grep -q 'p3SupersingularPi0IsNotExponentResidual' "${residual_targets[2]}"
grep -q 'p11EqualCountDoesNotCreateExponentOrbitSameObject' "${residual_targets[2]}"


# Small-characteristic isotropy-order attribution + marked-cover acquisition pattern.
isotropy_targets=(
  DASHI/Moonshine/OggSmallCharacteristicAutomorphismOrderAttributionExact.agda
  DASHI/Moonshine/OggSmallCharacteristicIsotropyOrderCrossPollinationExact.agda
  DASHI/Moonshine/OggSSPMarkedArithmeticResidualCoverPatternExact.agda
  DASHI/Moonshine/OggSSPExponentResidualArithmeticSourceInterfaceExact.agda
)

for target in "${isotropy_targets[@]}"; do
  test -f "$target"
done

scripts/run_agda29_parallel_check.sh "${isotropy_targets[@]}"

grep -q 'p2ExternalAutomorphismOrderIs24' "${isotropy_targets[0]}"
grep -q 'p3ExternalAutomorphismOrderIs12' "${isotropy_targets[0]}"
grep -q 'p2OrderIsTwiceP3Order' "${isotropy_targets[0]}"

grep -q 'p2ExternalOrderMatchesBinaryTetrahedralSkeleton' "${isotropy_targets[1]}"
grep -q 'p3ExternalOrderMatchesRotationalTetrahedralSkeleton' "${isotropy_targets[1]}"
grep -q 'factorTwoDoesNotIdentifyRetainedOrientationFibre' "${isotropy_targets[1]}"

grep -q 'markedSymmetryChangesResidual' "${isotropy_targets[2]}"
grep -q 'markedCoverProjectionIsNotInjective' "${isotropy_targets[2]}"
grep -q 'p11PatternReceipt' "${isotropy_targets[2]}"

grep -q 'MarkedCoverArithmeticResidualSourceCandidate' "${isotropy_targets[3]}"
grep -q 'markedCoverAcquisitionPatternAvailable' "${isotropy_targets[3]}"


# Raw finite-field candidate asymmetry: p2 requires enrichment, p3 admits quotient.
acquisition_targets=(
  DASHI/Moonshine/OggSSPP2F4FrobeniusCandidateNoGoExact.agda
  DASHI/Moonshine/OggSSPP3F9FrobeniusCandidateNoGoExact.agda
  DASHI/Moonshine/OggSSPSmallCharacteristicAcquisitionDirectionExact.agda
  DASHI/Moonshine/OggSSPExponentResidualArithmeticSourceInterfaceExact.agda
)

for target in "${acquisition_targets[@]}"; do
  test -f "$target"
done

scripts/run_agda29_parallel_check.sh "${acquisition_targets[@]}"

grep -q 'f4Pi0Count' "${acquisition_targets[0]}"
grep -q 'noUniformThreeOrbitLiftToTen' "${acquisition_targets[0]}"
grep -q 'stratifiedMarkedRefinementRequiredIfRefiningF4Orbits' "${acquisition_targets[0]}"

grep -q 'f9ExtensionCoordinateOrbitRecognition' "${acquisition_targets[1]}"
grep -q 'f9ExtensionCoordinateNotPi0Embedding' "${acquisition_targets[1]}"
grep -q 'noFullF9FrobeniusRecognitionToP3' "${acquisition_targets[1]}"

grep -q 'p2AcquisitionDirection' "${acquisition_targets[2]}"
grep -q 'p3AcquisitionDirection' "${acquisition_targets[2]}"
grep -q 'p2NoUniformMarkedLift' "${acquisition_targets[2]}"
grep -q 'p3ConcreteQuotientExists' "${acquisition_targets[2]}"

grep -q 'preferredAcquisitionDirection' "${acquisition_targets[3]}"
grep -q 'p2AcquisitionDirectionIsMarkedEnrichment' "${acquisition_targets[3]}"
grep -q 'p3AcquisitionDirectionIsQuotient' "${acquisition_targets[3]}"


# RH sparse balanced-ternary / 3-adic cross-pollination.
rh_ternary_targets=(
  DASHI/Analysis/RiemannOneTwoThreeCoefficientLanguageExact.agda
  DASHI/Analysis/RiemannPrimitiveKernelBalancedTernaryStencilExact.agda
  DASHI/Analysis/RiemannMonster196830TernaryShiftBridgeExact.agda
)

for target in "${rh_ternary_targets[@]}"; do
  test -f "$target"
done

scripts/run_agda29_parallel_check.sh "${rh_ternary_targets[@]}"

grep -q 'ratioCrossMultiplicationExact' "${rh_ternary_targets[0]}"
grep -q 'twentyBalancedIsTwenty' "${rh_ternary_targets[0]}"

grep -q 'poleCoefficientIs80' "${rh_ternary_targets[1]}"
grep -q 'jCoefficientDepthFive' "${rh_ternary_targets[1]}"
grep -q 'canonicalPrimitiveKernelThreeAdicProfile' "${rh_ternary_targets[1]}"
grep -q 'evaluationAtThreeDoesNotIdentifyGoldenRatioDynamics' "${rh_ternary_targets[1]}"

grep -q 'structuredBulkAtDepthFive' "${rh_ternary_targets[2]}"
grep -q 'depthFiveResidualFactorsFourShift' "${rh_ternary_targets[2]}"
grep -q 'sameFourShiftDoesNotImplySameObject' "${rh_ternary_targets[2]}"


# Primitive-row Smith invariant versus coordinate 3-adic filtration.
rh_smith_targets=(
  DASHI/Analysis/RiemannPrimitiveKernelUnimodularBasisExact.agda
  DASHI/Analysis/RiemannPrimitiveKernelExplicitSmithReductionExact.agda
  DASHI/Analysis/RiemannPrimitiveKernelFiltrationTransportExact.agda
  DASHI/Analysis/RiemannPrimitiveKernelSmithFiltrationSeparationExact.agda
)

for target in "${rh_smith_targets[@]}"; do
  test -f "$target"
done

scripts/run_agda29_parallel_check.sh "${rh_smith_targets[@]}"

grep -q 'determinantUIsOne' "${rh_smith_targets[0]}"
grep -q 'transformedLeadingPairExact' "${rh_smith_targets[0]}"
grep -q 'primitiveBezoutCertificate' "${rh_smith_targets[0]}"
grep -q 'depthProfileChangesUnderUnimodularBasis' "${rh_smith_targets[0]}"

grep -q 'explicitSmithNormalForm' "${rh_smith_targets[1]}"
grep -q 'rowMapHasPreimage' "${rh_smith_targets[1]}"

grep -q 'canonicalKernelCorrespondence' "${rh_smith_targets[2]}"
grep -q 'coordinateAxesDoNotBecomeIntrinsicKernel' "${rh_smith_targets[2]}"

grep -q 'primitiveSmithStyleReceipt' "${rh_smith_targets[3]}"
grep -q 'explicitSmithNormalFormOwned' "${rh_smith_targets[3]}"
grep -q 'rowMapSurjectiveWitness' "${rh_smith_targets[3]}"
grep -q 'filteredKernelIsPreferredInvariantObject' "${rh_smith_targets[3]}"


# RH filtered provenance through the existing 15SSP finite machinery.
rh_ssp15_targets=(
  DASHI/Analysis/RiemannSSP15DepthFiveRoleCodecExact.agda
  DASHI/Analysis/RiemannSSP15SignedProvenanceBridgeExact.agda
  DASHI/Analysis/RiemannSSP15PartitionSeparationExact.agda
  DASHI/Analysis/RiemannSSP15ChosenGridTransversalityExact.agda
  DASHI/Analysis/RiemannSSP15FilteredProvenanceCapstoneExact.agda
  DASHI/Analysis/RiemannSSP15RoleCMContingencyExact.agda
  DASHI/Analysis/RiemannSSP15ProducerMarkedSignedFRACTRANExact.agda
)

for target in "${rh_ssp15_targets[@]}"; do
  test -f "$target"
done

scripts/run_agda29_parallel_check.sh "${rh_ssp15_targets[@]}"

grep -q 'decodeAfterEncode' "${rh_ssp15_targets[0]}"
grep -q 'fiveModesTimesThreeRolesIsFifteen' "${rh_ssp15_targets[0]}"
grep -q 'roleToPhaseIntertwinesReversal' "${rh_ssp15_targets[0]}"

grep -q 'roleCodePointedRoundTrip' "${rh_ssp15_targets[1]}"
grep -q 'jRoleValuationZeroAt' "${rh_ssp15_targets[1]}"
grep -q 'jColumnNeutralPrimesExact' "${rh_ssp15_targets[1]}"
grep -q 'jColumnFiveDistinctPointedStatesShareZeroValuation' "${rh_ssp15_targets[1]}"
grep -q 'attachedRoleReopensCode' "${rh_ssp15_targets[1]}"

grep -q 'cmAndHeckeAlreadyProvedDistinct' "${rh_ssp15_targets[2]}"
grep -q 'equalFifteenTotalsDoNotCreateSamePartition' "${rh_ssp15_targets[2]}"

grep -q 'originRoleColumnNotSingleCMClass' "${rh_ssp15_targets[3]}"
grep -q 'jRoleColumnNotSingleCMClass' "${rh_ssp15_targets[3]}"
grep -q 'sRoleColumnNotSingleCMClass' "${rh_ssp15_targets[3]}"
grep -q 'chosenInternalModeNotPrimeNativeComplementMode' "${rh_ssp15_targets[3]}"

grep -q 'PrimitiveRowProducerRoleCertificate' "${rh_ssp15_targets[4]}"
grep -q 'producerMarkedRoundTripAtRoleCode' "${rh_ssp15_targets[4]}"
grep -q 'producerRoleCertificateInhabitedHere' "${rh_ssp15_targets[4]}"


grep -q 'completeThreeByThreeCountTableOwned' "${rh_ssp15_targets[5]}"
grep -q 'splitColumnMatchesCanonicalCMCount' "${rh_ssp15_targets[5]}"
grep -q 'inertColumnMatchesCanonicalCMCount' "${rh_ssp15_targets[5]}"
grep -q 'ramifiedColumnMatchesCanonicalCMCount' "${rh_ssp15_targets[5]}"


# Pinned cross-branch RH producer donor provenance.
rh_ssp15_donor_target=DASHI/Analysis/RiemannSSP15RHProducerDonorManifestExact.agda
test -f "$rh_ssp15_donor_target"
scripts/run_agda29_parallel_check.sh "$rh_ssp15_donor_target"
grep -q '824f84cddf5cf424c643688c2d24e351795dac07' "$rh_ssp15_donor_target"
grep -q '138153858e329469048175fcdeeaf75c182078be' "$rh_ssp15_donor_target"
grep -q 'quarticFourAtomic_primitive_integer_kernel' "$rh_ssp15_donor_target"
grep -q 'quarticFourAtomic_depth_five_block_kernel' "$rh_ssp15_donor_target"
grep -q 'exactHeadVerifierObservedIsFalse' "$rh_ssp15_donor_target"


grep -q 'producerMarkedHyperformLane' "${rh_ssp15_targets[6]}"
grep -q 'originRoleHyperformOrientationInverse' "${rh_ssp15_targets[6]}"
grep -q 'jRoleProgramIsEmpty' "${rh_ssp15_targets[6]}"
grep -q 'jAllExecutionEffectsCoincide' "${rh_ssp15_targets[6]}"
grep -q 'producerMarkedSeedReopensRoleCode' "${rh_ssp15_targets[6]}"
