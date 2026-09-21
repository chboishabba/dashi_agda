module DASHI.Physics.Closure.NSABCDConcentratedCompletionCutExact where

------------------------------------------------------------------------
-- NAVIER--STOKES A/B/C/D CONCENTRATED COMPLETION CUT
--
-- This owner is intentionally non-promoting.  It records the post-portability
-- theorem frontier after:
--
-- A: canonical R3 same-output carrier + signed resolvent split + compensated
--    Lebesgue second-moment compiler;
-- B: lattice-paid state variation + same-displacement A2 + preferred one-sided
--    finite second-moment coefficient, including the exact 3 E0 specialization;
-- C/D: canonical Fefferman semantics + native released-comparator adapters +
--      explicit either-C-or-D terminal cut.
--
-- It exists to prevent historical false flags from being read as the current
-- global frontier.  The booleans below mean only what their names say.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR571PreferredOneSidedSecondMomentExact as BSharp
import DASHI.Physics.Closure.NSTriadKNR571PhysicalWeightedSecondMomentEndgameExact as BEnd
import DASHI.Physics.Closure.NSWholeSpaceSignedLebesgueEndgameExact as AEnd
import DASHI.Physics.Closure.NSOpenAI2026ReleasedCDNativeAnyOneCutExact as CD
import DASHI.Physics.Closure.NSTriadKNR571PhysicalSecondMomentSummationExact as BSum
import DASHI.Physics.Closure.NSTriadKNR571SecondMomentToR568BridgeExact as BR568
import DASHI.Physics.Closure.NSWholeSpaceCompensatedMajorantLowHighGlueExact as AGlue
import DASHI.Physics.Closure.NSWholeSpacePhysicalCompensatedFieldCompilerExact as AField
import DASHI.Physics.Closure.NSOpenAI2026ReleasedCovarianceMovingNativeExact as Cov
import DASHI.Physics.Closure.NSOpenAI2026ReleasedOptionCCompactCandidateAdapterExact as CAdapter
import DASHI.Physics.Closure.NSOpenAI2026ReleasedOptionDPeriodicCandidateAdapterExact as DAdapter
import DASHI.Physics.Closure.NSConcreteReleasedCandidateAdaptersExact as Candidate
import DASHI.Physics.Closure.NSTriadKNR567ToLiteralR571M2Exact as BR567
import DASHI.Physics.Closure.NSWholeSpaceLowHighConvolutionProducerExact as AConv
import DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedPeriodicCandidateNativeExact as DSelected
import DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedCompactCandidateFromPeriodicExact as CSelected
import DASHI.Physics.Closure.NSOpenAI2026ReleasedPeriodicExclusionNativeExact as DExclude
import DASHI.Physics.Closure.NSOpenAI2026ReleasedR3FiniteEnergyExclusionNativeExact as CExclude
import DASHI.Physics.Closure.NSTriadKNR571UnitNormalizedDisplacementWeldExact as BNorm
import DASHI.Physics.Closure.NSTriadKNR573HomochiralHeterochiralSplitExact as B573Split
import DASHI.Physics.Closure.NSTriadKNR573HelicitySplitLowOutputPaymentExact as B573Pay
import DASHI.Physics.Closure.NSTriadKNNestedSlotThreeClassNormCompilerRound587Exact as B587
import DASHI.Physics.Closure.NSTriadKNR587ExactThreeClassSelfBudgetBidiExact as B587Self
import DASHI.Physics.Closure.NSTriadKNR567HelicityResolvedForcingSquareExact as BHelicity
import DASHI.Physics.Closure.NSTriadKNR571OppositeShiftMidpointObstructionExact as BMidpoint
import DASHI.Physics.Closure.NSTriadKNR540PhysicalOffDiagonalR571M2Exact as BR540Physical
import DASHI.Physics.Closure.NSTriadKNFourSignInnerFibreGramBoundaryRound577Exact as BR577
import DASHI.Physics.Closure.NSTriadKNR571PhysicalM2DissipationFoldExact as BFold
import DASHI.Physics.Closure.NSWholeSpacePhysicalMajorantDominationExact as ADom
import DASHI.Physics.Closure.NSOpenAI2026ReleasedPeriodicEnergyUniquenessKernelExact as DEnergy
import DASHI.Physics.Closure.NSOpenAI2026ReleasedCompactLocalizationKernelExact as CLocal
import DASHI.Physics.Closure.NSTriadKNR567ForcingCellPhysicalEnvelopeExact as B567Envelope
import DASHI.Physics.Closure.NSTriadKNSameOutputIncidenceDisplacementExact as BDisplacement
import DASHI.Physics.Closure.NSTriadKNR540OffDiagonalToLiteralR571M2Exact as BOffdiagM2
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as BRateDiff
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceQuantitativePairBoundExact as BQuantPair
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBudgetExact as BCoherentBudget
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as BCoherentLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceVectorCenteringExact as BVectorCenter
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceVectorLiveExact as BVectorLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceVectorResidualWeldExact as BVectorWeld
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredInputLaplacianVectorResidualExact as BInputVector
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianR440WeldExact as BInputR440
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredInputLaplacianBonyVectorExact as BBonyVector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as BBonyLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredBonyCovariancePaymentExact as BBonyPay
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCenteredBonyPaymentLiveExact as BBonyLivePay
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianBonyPairBlocksExact as BBonyPairs
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianThreeClassPairBlocksExact as BThreePairs
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceSixBlockLiveExact as BSixLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalSixBlockPaymentLiveExact as BSixPay
import DASHI.Physics.Closure.NSTriadKNPhysicalParabolicCriticalRegionRoutingExact as BRegionRoute
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact as BRegionPairs
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceCriticalRegionLiveExact as BRegionLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as BRegionPay
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionToR432Exact as BRegionR432
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionUniformFamilyExact as BRegionFamily
import DASHI.Physics.Closure.NSTriadKNFiniteBipartiteCovarianceExact as BBipartite
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionFilteredExact as BFilteredRegion
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceFilteredRegionLiveExact as BFilteredLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowFractionalShellPaymentExact as BDeepFL
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowDeepHHFractionalShellPaymentExact as BDeepCross
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepHHFractionalShellPaymentExact as BDeepHH
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRelativeCovarianceExact as BCriticalTouch
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionUniformFamilyProducerExact as BUniformProducer
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DecompositionExact as BR406Decomp

------------------------------------------------------------------------
-- A
------------------------------------------------------------------------

aCanonicalContinuousSignedCarrierClosed : Bool
aCanonicalContinuousSignedCarrierClosed = true

aLebesgueSignedAggregationCompilerClosed : Bool
aLebesgueSignedAggregationCompilerClosed =
  AEnd.wholeSpaceLebesgueAggregationCompilerClosed

aLowFrequencyCompensationOrderingClosed : Bool
aLowFrequencyCompensationOrderingClosed =
  AEnd.wholeSpaceLowFrequencyCompensationBeforeIntegrationClosed

aLowHighIntegrabilityGlueClosed : Bool
aLowHighIntegrabilityGlueClosed =
  AGlue.lowHighIntegrabilityGlueClosed

aCompensatedFieldFromLowHighCompilerClosed : Bool
aCompensatedFieldFromLowHighCompilerClosed =
  AField.lowHighPiecesCompileExactCompensatedField

aLowConvolutionTargetIsolated : Bool
aLowConvolutionTargetIsolated =
  AConv.lowCompensatedConvolutionTargetIsolated

aHighInverseSixthTargetIsolated : Bool
aHighInverseSixthTargetIsolated =
  AConv.highInverseSixthConvolutionTargetIsolated

aPhysicalMajorantIntegrabilityReducedToEnvelopeDomination : Bool
aPhysicalMajorantIntegrabilityReducedToEnvelopeDomination =
  ADom.physicalMajorantIntegrabilityNoLongerOpaque

aLowConvolutionEnvelopeIntegrableClosed : Bool
aLowConvolutionEnvelopeIntegrableClosed = false

aHighInverseSixthEnvelopeIntegrableClosed : Bool
aHighInverseSixthEnvelopeIntegrableClosed = false

aLowPhysicalMajorantProducerClosed : Bool
aLowPhysicalMajorantProducerClosed = false

aHighPhysicalMajorantProducerClosed : Bool
aHighPhysicalMajorantProducerClosed = false

aPhysicalCompensatedMajorantProducerClosed : Bool
aPhysicalCompensatedMajorantProducerClosed = false

aLiteralClayTheoremClosed : Bool
aLiteralClayTheoremClosed = false

------------------------------------------------------------------------
-- B
------------------------------------------------------------------------

bDiscreteStateVariationClosed : Bool
bDiscreteStateVariationClosed =
  BEnd.periodicStateVariationPaidByLatticeGap

bSameDisplacementA2Closed : Bool
bSameDisplacementA2Closed =
  BEnd.periodicA2UsesSamePhysicalDisplacement

bUnitNormalizedLiveLatticeDisplacementWeldClosed : Bool
bUnitNormalizedLiveLatticeDisplacementWeldClosed =
  BNorm.unitNormalizedLiveLatticeDisplacementWeldClosed

bA1A2G2SameDisplacementUnderPhysicalNormalization : Bool
bA1A2G2SameDisplacementUnderPhysicalNormalization =
  BNorm.a1A2G2UseOneDisplacementUnderUnitNormalization

bR573LiteralFourChannelHelicitySplitClosed : Bool
bR573LiteralFourChannelHelicitySplitClosed =
  B573Split.r573LiteralFourSignHelicitySplitClosed

bR567ForcingFullHelicityResolvedClosed : Bool
bR567ForcingFullHelicityResolvedClosed =
  BHelicity.r567ForcingFullHelicityResolvedExactly

bR573HomochiralPointwiseLowOutputPaymentClosed : Bool
bR573HomochiralPointwiseLowOutputPaymentClosed =
  B573Pay.r573HomochiralPointwiseLowOutputPaymentClosed

bR573HeterochiralPointwiseLowOutputPaymentClosed : Bool
bR573HeterochiralPointwiseLowOutputPaymentClosed =
  B573Pay.r573HeterochiralPointwiseLowOutputPaymentClosed

bR573HeterochiralPointwisePaymentRequiresHH : Bool
bR573HeterochiralPointwisePaymentRequiresHH =
  B573Pay.r573HeterochiralPaymentRequiresHH

bR573HomochiralPointwisePaymentRequiresMidpoint : Bool
bR573HomochiralPointwisePaymentRequiresMidpoint =
  B573Pay.r573HomochiralPaymentRequiresMidpoint

bLiveNestedThreeClassCompilerClosed : Bool
bLiveNestedThreeClassCompilerClosed =
  B587.round587PreferredLiveInnerClassCountIsThree

bLiveNestedThreeClassBudgetRecordsInhabited : Bool
bLiveNestedThreeClassBudgetRecordsInhabited =
  B587Self.r587ThreeDependentClassBudgetRecordsInhabited

bLiveNestedThreeClassUsefulUniformMajorantsPaid : Bool
bLiveNestedThreeClassUsefulUniformMajorantsPaid =
  B587Self.r587ExactSelfBudgetsAreUsefulUniformMajorants

bLiveNestedThreeClassRemainingDebtIsUniformMajorization : Bool
bLiveNestedThreeClassRemainingDebtIsUniformMajorization =
  B587Self.r587RemainingDebtIsUniformMajorizationNotRecordConstruction

bOuterSpectatorWeightedSpacetimePaymentClosed : Bool
bOuterSpectatorWeightedSpacetimePaymentClosed =
  B587.round587OuterWeightSpectatorSpacetimeClosed

bOppositeShiftMidpointNecessityClosed : Bool
bOppositeShiftMidpointNecessityClosed =
  BMidpoint.oppositeShiftMidpointNecessityClosed

bGlobalR567CellToCenteredR571SampleIsValidWithoutMidpoint : Bool
bGlobalR567CellToCenteredR571SampleIsValidWithoutMidpoint = false

bR540PhysicalOffDiagonalCarrierInstantiated : Bool
bR540PhysicalOffDiagonalCarrierInstantiated =
  BR540Physical.physicalR540CarrierInstantiated

bR540PhysicalOutputFibreUniquenessDischarged : Bool
bR540PhysicalOutputFibreUniquenessDischarged =
  BR540Physical.physicalOutputFibreUniquenessDischarged

bLiteralR396RemainderToPreferredM2CompilerClosed : Bool
bLiteralR396RemainderToPreferredM2CompilerClosed =
  BR540Physical.literalR396RemainderLandsInPreferredM2GivenPairRealization

bR577FourSignCellMassPaidByEnergyDissipationKernel : Bool
bR577FourSignCellMassPaidByEnergyDissipationKernel =
  BR577.round577CellMassMajorantPaidByEnergyDissipationKernel

bR577VariableFibreReducedToEDPlusOneGramResidual : Bool
bR577VariableFibreReducedToEDPlusOneGramResidual =
  BR577.round577VariableFibreReducedToEDPlusOneGramResidual

bR577SignedGramResidualClosed : Bool
bR577SignedGramResidualClosed = false

bD1b2PhysicalFixedOutputRateDifferenceFactored : Bool
bD1b2PhysicalFixedOutputRateDifferenceFactored =
  BRateDiff.fixedOutputPhysicalRateDifferenceFactored

bD1b2SamePairAbsoluteQuantitativeBoundClosed : Bool
bD1b2SamePairAbsoluteQuantitativeBoundClosed =
  BQuantPair.absolutePairDifferenceSameGraphBoundClosed

bD1b2PhysicalSignedPairBudgetClosed : Bool
bD1b2PhysicalSignedPairBudgetClosed =
  BCoherentBudget.physicalSignedCoherentPairBudgetClosed

bD1b2PhysicalFixedOutputFamilyBudgetSummed : Bool
bD1b2PhysicalFixedOutputFamilyBudgetSummed =
  BCoherentBudget.physicalFixedOutputFamilyBudgetSummedHere

bD1b2LivePhysicalCoherentCovarianceReductionClosed : Bool
bD1b2LivePhysicalCoherentCovarianceReductionClosed =
  BCoherentLive.livePhysicalCoherentCovarianceQuantitativeReductionClosed

bD1b2CompleteGraphComplex3VectorIdentityClosed : Bool
bD1b2CompleteGraphComplex3VectorIdentityClosed =
  BVectorCenter.completeGraphVectorCovarianceIdentityClosed

bD1b2LiveCovarianceCollapsedToSingleCenteredVector : Bool
bD1b2LiveCovarianceCollapsedToSingleCenteredVector =
  BVectorLive.liveCoherentCovarianceVectorReductionClosed

bD1b2CompleteGraphVectorEqualsCenteredResidual : Bool
bD1b2CompleteGraphVectorEqualsCenteredResidual =
  BVectorWeld.completeGraphVectorSameObjectWeldClosed

bD1b2CenteredResidualEqualsTwiceInputLaplacianResidual : Bool
bD1b2CenteredResidualEqualsTwiceInputLaplacianResidual =
  BInputVector.centeredInputLaplacianVectorIdentityClosed

bD1b2InputLaplacianWeightIsSwapInvariant : Bool
bD1b2InputLaplacianWeightIsSwapInvariant =
  BInputR440.inputLaplacianWeightIsSwapInvariant

bD1b2InputWeightedAmplitudeOnCanonicalR440Carrier : Bool
bD1b2InputWeightedAmplitudeOnCanonicalR440Carrier =
  BInputR440.inputWeightedAmplitudeIsLiteralR440Aggregate

bD1b2PairwiseYoungFamilyRequiredForPrimaryRoute : Bool
bD1b2PairwiseYoungFamilyRequiredForPrimaryRoute =
  BVectorLive.pairwiseYoungFamilyRequiredForPrimaryD1b2Route

bD1b2CenteredInputLaplacianExactFourClassVectorSplitClosed : Bool
bD1b2CenteredInputLaplacianExactFourClassVectorSplitClosed =
  BBonyVector.centeredInputLaplacianFourClassVectorSplitClosed

bD1b2CenteredInputLaplacianExactThreeClassVectorSplitClosed : Bool
bD1b2CenteredInputLaplacianExactThreeClassVectorSplitClosed =
  BBonyVector.centeredInputLaplacianThreeClassVectorSplitClosed

bD1b2LiveCovarianceExactThreeCenteredBonyWorkSplitClosed : Bool
bD1b2LiveCovarianceExactThreeCenteredBonyWorkSplitClosed =
  BBonyLive.liveD1b2ExactThreeCenteredBonyWorkSplitClosed

bD1b2BonySplitUsesClassLocalCentering : Bool
bD1b2BonySplitUsesClassLocalCentering =
  BBonyLive.liveD1b2BonySplitUsesClassLocalCentering

bD1b2CenteredBonyQuantitativeCompilerClosed : Bool
bD1b2CenteredBonyQuantitativeCompilerClosed =
  BBonyPay.centeredBonyCovariancePaymentCompilerClosed

bD1b2IndexedPhysicalCenteredBonyPaymentSocketClosed : Bool
bD1b2IndexedPhysicalCenteredBonyPaymentSocketClosed =
  BBonyLivePay.liveCenteredBonyPhysicalPaymentCompilerClosed

bD1b2CenteredBonyFarLowSignedProducerClosed : Bool
bD1b2CenteredBonyFarLowSignedProducerClosed = false

bD1b2CenteredBonyHighHighSignedProducerClosed : Bool
bD1b2CenteredBonyHighHighSignedProducerClosed = false

bD1b2CenteredBonyCriticalCoreSignedProducerClosed : Bool
bD1b2CenteredBonyCriticalCoreSignedProducerClosed = false


-- Safer quantitative normal form: retain multiplier differences at pair level
-- rather than estimating globally-centered class vectors separately.
bD1b2CompletePairGraphSixBonyBlocksClosed : Bool
bD1b2CompletePairGraphSixBonyBlocksClosed =
  BThreePairs.completePairGraphThreeClassSixBlockLedgerClosed

bD1b2LiveCovarianceSixSignedBonyPairBlocksClosed : Bool
bD1b2LiveCovarianceSixSignedBonyPairBlocksClosed =
  BSixLive.liveD1b2SixSignedThreeClassPairBlockNormalFormClosed

bD1b2SafeSixBlockPaymentCompilerClosed : Bool
bD1b2SafeSixBlockPaymentCompilerClosed =
  BSixPay.liveSixBlockPaymentCompilerClosed

bD1b2LiteralR236PhysicalRegionClassifierClosed : Bool
bD1b2LiteralR236PhysicalRegionClassifierClosed =
  BRegionRoute.literalR236PhysicalRegionClassifierClosed

bD1b2LiteralR236RegionPairLedgerClosed : Bool
bD1b2LiteralR236RegionPairLedgerClosed =
  BRegionPairs.literalCriticalRegionPairLedgerClosed

bD1b2LiveCovarianceLiteralR236SixBlockNormalFormClosed : Bool
bD1b2LiveCovarianceLiteralR236SixBlockNormalFormClosed =
  BRegionLive.liveD1b2PhysicalR236SixBlockNormalFormClosed

bD1b2LivePhysicalCriticalRegionPaymentCompilerClosed : Bool
bD1b2LivePhysicalCriticalRegionPaymentCompilerClosed =
  BRegionPay.livePhysicalCriticalRegionPaymentCompilerClosed


bD1b2LiveCriticalRegionToR432FixedOutputCompilerClosed : Bool
bD1b2LiveCriticalRegionToR432FixedOutputCompilerClosed =
  BRegionR432.liveCriticalRegionToR432FixedOutputCompilerClosed

bD1b2GlobalR406SameObjectWeldFromRegionPaymentsClosed : Bool
bD1b2GlobalR406SameObjectWeldFromRegionPaymentsClosed =
  BRegionR432.liveCriticalRegionToR432GlobalR406SameObjectWeldClosedHere


bD1b2NativeR236UniformOutputFamilySummationClosed : Bool
bD1b2NativeR236UniformOutputFamilySummationClosed =
  BRegionFamily.nativeR236UniformFamilySummationClosed

bD1b2NativeR236OutputSummationAddsCardinalityFactor : Bool
bD1b2NativeR236OutputSummationAddsCardinalityFactor =
  BRegionFamily.nativeR236OutputSummationAddsCardinalityFactor

bD1b2NativeR236GlobalEDRoutingUsesExistingR469R219 : Bool
bD1b2NativeR236GlobalEDRoutingUsesExistingR469R219 =
  BRegionFamily.nativeR236GlobalEDRoutingUsesExistingR469R219

bD1b2NativeR236UniformFamilyProducerInhabited : Bool
bD1b2NativeR236UniformFamilyProducerInhabited =
  BRegionFamily.nativeR236UniformFamilyProducerInhabitedHere


bD1b2FiniteBipartiteCovarianceClosedFormClosed : Bool
bD1b2FiniteBipartiteCovarianceClosedFormClosed =
  BBipartite.finiteBipartiteCovarianceClosedFormClosed

bD1b2FilteredPhysicalR236CovarianceDecompositionClosed : Bool
bD1b2FilteredPhysicalR236CovarianceDecompositionClosed =
  BFilteredRegion.filteredPhysicalCriticalRegionCovarianceDecompositionClosed

bD1b2FilteredPhysicalR236RegionMembershipCarriesEvidence : Bool
bD1b2FilteredPhysicalR236RegionMembershipCarriesEvidence = true

bD1b2LiveCovarianceFilteredPhysicalR236NormalFormClosed : Bool
bD1b2LiveCovarianceFilteredPhysicalR236NormalFormClosed =
  BFilteredLive.liveD1b2FilteredPhysicalRegionNormalFormClosed

bD1b2RemainingDeepRegionAnalysisIsFractionalShellDecay : Bool
bD1b2RemainingDeepRegionAnalysisIsFractionalShellDecay = true

bD1b2DeepFarLowShellFoldCompilerClosed : Bool
bD1b2DeepFarLowShellFoldCompilerClosed =
  BDeepFL.deepFarLowShellFoldCompilerClosed

bD1b2DeepFarLowDeepHHShellFoldCompilerClosed : Bool
bD1b2DeepFarLowDeepHHShellFoldCompilerClosed =
  BDeepCross.deepFarLowDeepHHBipartiteShellFoldClosed

bD1b2DeepHHShellFoldCompilerClosed : Bool
bD1b2DeepHHShellFoldCompilerClosed =
  BDeepHH.deepHHShellFoldClosed

bD1b2CriticalTouchingSignedOperatorCompilerClosed : Bool
bD1b2CriticalTouchingSignedOperatorCompilerClosed =
  BCriticalTouch.criticalTouchingSignedBlockOperatorCompilerClosed

bD1b2NativeR236UniformFamilyCompilerClosed : Bool
bD1b2NativeR236UniformFamilyCompilerClosed =
  BUniformProducer.uniformPhysicalCriticalRegionFamilyCompilerClosed

bD1b2NativeR236UniformAnalyticReceiptsInhabited : Bool
bD1b2NativeR236UniformAnalyticReceiptsInhabited =
  BUniformProducer.uniformPhysicalCriticalRegionFamilyAnalyticReceiptsInhabitedHere

bD1b2RegionPaymentsToR406DecompositionCompilerClosed : Bool
bD1b2RegionPaymentsToR406DecompositionCompilerClosed =
  BR406Decomp.criticalRegionR406DecompositionCompilerClosed

bD1b2LiteralR406SameObjectEqualityInhabited : Bool
bD1b2LiteralR406SameObjectEqualityInhabited =
  BR406Decomp.literalR406SameObjectEqualityInhabitedHere

bD1b2DeepOnlySignedRegionPaymentsClosed : Bool
bD1b2DeepOnlySignedRegionPaymentsClosed = false

bD1b2CriticalTouchingRelativeCovarianceClosed : Bool
bD1b2CriticalTouchingRelativeCovarianceClosed = false

bD1b2QuantitativeR440InputLaplacianCovariancePaymentClosed : Bool
bD1b2QuantitativeR440InputLaplacianCovariancePaymentClosed = false

bD1b2CenteredPhysicalPairFamilyCutoffUniformPaymentClosed : Bool
bD1b2CenteredPhysicalPairFamilyCutoffUniformPaymentClosed = false

bCutoffUniformG1FamilyEnvelopeClosed : Bool
bCutoffUniformG1FamilyEnvelopeClosed = false

bPreferredDuplicateCurvatureRemoved : Bool
bPreferredDuplicateCurvatureRemoved =
  BSharp.genericDuplicateCurvatureChargeRemoved

bThreeEnergyCoefficientClosed : Bool
bThreeEnergyCoefficientClosed =
  BSharp.periodicCoefficientThreeEnergyProved

bSamplewiseM2SummationCompilerClosed : Bool
bSamplewiseM2SummationCompilerClosed =
  BSum.samplewisePhysicalM2PaymentSuffices

bM2ToR568CompilerClosed : Bool
bM2ToR568CompilerClosed =
  BR568.r571PhysicalM2ToR568CompilerClosed

bR567CompleteSquareAggregationClosed : Bool
bR567CompleteSquareAggregationClosed =
  BR567.r567CompleteSquareAggregationClosed

-- Corrected September-20 cut: the R571 displacement-weighted M2 belongs on
-- the literal duplicate-free ordered off-diagonal carrier.  The completed
-- R567 square contains diagonal cells with displacement zero and is therefore
-- not the canonical pointwise M2 consumer.
bR567ForcingCellPositivePhysicalEnvelopeClosed : Bool
bR567ForcingCellPositivePhysicalEnvelopeClosed =
  B567Envelope.r567LiteralForcingCellPositiveEnvelopeClosed

bSameOutputIncidenceOppositeShiftClosed : Bool
bSameOutputIncidenceOppositeShiftClosed =
  BDisplacement.sameOutputIncidenceOppositeShiftClosed

bDistinctOffDiagonalDisplacementNonzeroClosed : Bool
bDistinctOffDiagonalDisplacementNonzeroClosed =
  BDisplacement.distinctOffDiagonalDisplacementNonzeroClosed

bR540OrderedOffDiagonalM2CompilerClosed : Bool
bR540OrderedOffDiagonalM2CompilerClosed =
  BOffdiagM2.r540OrderedOffDiagonalM2CompilerClosed

bR540OrderedOffDiagonalM2IntroducesCardinalityTax : Bool
bR540OrderedOffDiagonalM2IntroducesCardinalityTax =
  BOffdiagM2.r540OrderedOffDiagonalM2IntroducesCardinalityTax

bR567FullSquarePointwiseM2IsCanonicalConsumer : Bool
bR567FullSquarePointwiseM2IsCanonicalConsumer =
  BOffdiagM2.r567FullSquarePointwiseM2IsCanonicalConsumer

bR567CellToR571SampleSameObjectClosed : Bool
bR567CellToR571SampleSameObjectClosed = false

bR567CellBelowR571PairedMagnitudeClosed : Bool
bR567CellBelowR571PairedMagnitudeClosed = false

bForcingSquareBelowLiteralM2Closed : Bool
bForcingSquareBelowLiteralM2Closed = false

bCardinalityFreeM2DissipationFoldCompilerClosed : Bool
bCardinalityFreeM2DissipationFoldCompilerClosed =
  BFold.cardinalityFreeFiniteFoldClosed

bSamplewiseM2DissipationPaymentClosed : Bool
bSamplewiseM2DissipationPaymentClosed = false

bLiteralM2FoldIntoGalerkinDissipationClosed : Bool
bLiteralM2FoldIntoGalerkinDissipationClosed = false

bCutoffUniformIntegratedM2PaymentClosed : Bool
bCutoffUniformIntegratedM2PaymentClosed = false

bPhysicalWeightedSecondMomentPaymentClosed : Bool
bPhysicalWeightedSecondMomentPaymentClosed = false

bLiteralClayTheoremClosed : Bool
bLiteralClayTheoremClosed = false

------------------------------------------------------------------------
-- C / D
------------------------------------------------------------------------

cdCanonicalConcreteSemanticsClosed : Bool
cdCanonicalConcreteSemanticsClosed =
  CD.canonicalConcreteSemanticsAtReleasedBoundary

cReleasedComparatorAdapterClosed : Bool
cReleasedComparatorAdapterClosed =
  CD.releasedComparatorAdapterToLiteralCClosed

dReleasedComparatorAdapterClosed : Bool
dReleasedComparatorAdapterClosed =
  CD.releasedComparatorAdapterToLiteralDClosed

cdEitherNativeTheoremSuffices : Bool
cdEitherNativeTheoremSuffices =
  CD.eitherReleasedAlternativeSuffices

cdReleasedCovarianceMovingBodyPorted : Bool
cdReleasedCovarianceMovingBodyPorted =
  Cov.releasedCovarianceMovingBodyPorted

cCompactCandidateComparatorAdapterClosed : Bool
cCompactCandidateComparatorAdapterClosed =
  CAdapter.releasedOptionCCompactCandidateAdapterBodyPorted

dPeriodicCandidateComparatorAdapterClosed : Bool
dPeriodicCandidateComparatorAdapterClosed =
  DAdapter.releasedOptionDPeriodicCandidateAdapterBodyPorted

cCandidateFamilyToLiteralCompilerClosed : Bool
cCandidateFamilyToLiteralCompilerClosed =
  Candidate.cComparatorWrapperRemovedFromFrontier

dCandidateFamilyToLiteralCompilerClosed : Bool
dCandidateFamilyToLiteralCompilerClosed =
  Candidate.dComparatorWrapperRemovedFromFrontier

dSelectedPeriodicCandidateBodyPorted : Bool
dSelectedPeriodicCandidateBodyPorted =
  DSelected.selectedPeriodicCandidateBodyPorted

dPeriodicGlobalExclusionBodyPorted : Bool
dPeriodicGlobalExclusionBodyPorted =
  DExclude.releasedCandidateExcludesGlobalSolutionBodyPorted

dPeriodicEnergyUniquenessCompositionClosed : Bool
dPeriodicEnergyUniquenessCompositionClosed =
  DEnergy.periodicEnergyUniquenessCompositionClosed

dPeriodicIBPAndGronwallProducersClosed : Bool
dPeriodicIBPAndGronwallProducersClosed = false

cSelectedCompactCandidateReusesD : Bool
cSelectedCompactCandidateReusesD =
  CSelected.cReusesSelectedPeriodicCandidate

cR3FiniteEnergyExclusionBodyPorted : Bool
cR3FiniteEnergyExclusionBodyPorted =
  CExclude.releasedR3FiniteEnergyExclusionBodyPorted

cCompactLocalizationAssemblyClosed : Bool
cCompactLocalizationAssemblyClosed =
  CLocal.cLocalizationAssemblyClosed

cCompactSupportResidualAndFiniteEnergyComparisonClosed : Bool
cCompactSupportResidualAndFiniteEnergyComparisonClosed = false

cActualCompactCandidateFamilyReconstructed : Bool
cActualCompactCandidateFamilyReconstructed = false

dActualPeriodicCandidateFamilyReconstructed : Bool
dActualPeriodicCandidateFamilyReconstructed = false

cReleasedAnalyticProofReconstructedInAgda : Bool
cReleasedAnalyticProofReconstructedInAgda = false

dReleasedAnalyticProofReconstructedInAgda : Bool
dReleasedAnalyticProofReconstructedInAgda = false

------------------------------------------------------------------------
-- Programme-level firewall.
------------------------------------------------------------------------

anyLiteralAlternativeClosedInAgdaHere : Bool
anyLiteralAlternativeClosedInAgdaHere = false

externalReceiptPromotedToAgdaProof : Bool
externalReceiptPromotedToAgdaProof = false

aDerivedFromB : Bool
aDerivedFromB = false

aLowHighIntegrabilityGlueClosedIsTrue :
  aLowHighIntegrabilityGlueClosed ≡ true
aLowHighIntegrabilityGlueClosedIsTrue = refl

bThreeEnergyCoefficientClosedIsTrue :
  bThreeEnergyCoefficientClosed ≡ true
bThreeEnergyCoefficientClosedIsTrue = refl

bM2ToR568CompilerClosedIsTrue :
  bM2ToR568CompilerClosed ≡ true
bM2ToR568CompilerClosedIsTrue = refl

cCompactCandidateComparatorAdapterClosedIsTrue :
  cCompactCandidateComparatorAdapterClosed ≡ true
cCompactCandidateComparatorAdapterClosedIsTrue = refl

dPeriodicCandidateComparatorAdapterClosedIsTrue :
  dPeriodicCandidateComparatorAdapterClosed ≡ true
dPeriodicCandidateComparatorAdapterClosedIsTrue = refl

cdEitherNativeTheoremSufficesIsTrue :
  cdEitherNativeTheoremSuffices ≡ true
cdEitherNativeTheoremSufficesIsTrue = refl

anyLiteralAlternativeClosedInAgdaHereIsFalse :
  anyLiteralAlternativeClosedInAgdaHere ≡ false
anyLiteralAlternativeClosedInAgdaHereIsFalse = refl

externalReceiptPromotedToAgdaProofIsFalse :
  externalReceiptPromotedToAgdaProof ≡ false
externalReceiptPromotedToAgdaProofIsFalse = refl

aDerivedFromBIsFalse : aDerivedFromB ≡ false
aDerivedFromBIsFalse = refl
