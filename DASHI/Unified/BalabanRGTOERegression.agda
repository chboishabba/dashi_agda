{-# OPTIONS --safe #-}
module DASHI.Unified.BalabanRGTOERegression where

open import Agda.Primitive using (Setω)

------------------------------------------------------------------------
-- TOE NORMALIZATION FOR THE BALABAN YANG--MILLS LANE
--
-- This module reuses existing theorem owners.
-- It does not replace source attribution.
-- It does not promote a finite or conditional result to continuum Yang--Mills.
--
-- Primary mathematical attribution remains in the imported owners.
-- Tadeusz Balaban owns the cited RG and localization source results.
-- Hall, Knapp, Higham, and the compact-Lie classification sources remain
-- credited by the existing Casimir owners.
-- DASHI owns only this import normalization and regression surface.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayLiteralWilsonP2NativeMeasureExact as NativeP2
import DASHI.Physics.YangMills.YMClayLiteralWilsonS2SameAlgebraBoundExact as P2Trace
import DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierExact as RouteS
import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as L31Probe
import DASHI.Physics.Foundations.TSFVFiltrationArrowLorentzBridgeExact as TSFVArrow
import DASHI.Physics.Foundations.TSFVKKSameMetricTransportExact as TSFVKKSameMetric
import DASHI.Physics.Foundations.TSVFMacroscopicSingleBranchRobustnessExact as TSVFMacro
import DASHI.Physics.Foundations.TSVFAdmissibleQuantumOverlapRobustnessExact as TSVFOverlap
import DASHI.Quantum.TSVFConcreteAdmissibleQubitABLExact as TSVFQubit
import DASHI.Quantum.TSVFComplexGammaProductBornExact as TSVFGamma
import DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact as TSVF2017Env
import DASHI.Quantum.TSVF2017OriginalComplexABLSelectedExact as TSVF2017ABL
import DASHI.Quantum.TSVF2017QuantitativeRateExact as TSVF2017Rate
import DASHI.Quantum.TSVF2017HeterogeneousEnvironmentABLExact as TSVFHeteroABL
import DASHI.Quantum.TSVF2017HeterogeneousRateExact as TSVFHeteroRate
import DASHI.Quantum.TSVF2017ControlledPointerRecordUnitaryExact as TSVFControlled
import DASHI.Physics.Foundations.TSVFOSSameSelectedClockIterateExact as TSVFOSClock
import DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact as YMKKHodge
import DASHI.Physics.YangMills.YMClayFiveSectorBidiSteelmanExact as FiveSectorBIDI
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicProductHaarExact as SUNVariableHaar
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGaugeHaarExact as SUNVariableGaugeHaar
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as SUNBondCodec
import DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact as SUNConstructedGauge
import DASHI.Physics.YangMills.YMClayNativeFiniteGaugeVectorNaturalitySafeExact as SUNFiniteSafe

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Density
import DASHI.Physics.YangMills.Balaban1989BetaHistoryToCanonicalCompleteDensityExact as CanonicalDensity
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as GeneratedDensity
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as StressScale
import DASHI.Physics.YangMills.BalabanCompactSimpleUniversalBetaFloorExact as BetaFloor
import DASHI.Physics.YangMills.BalabanCombinedRGUnifiedActionRound141Exact as CombinedAction
import DASHI.Physics.YangMills.BalabanPublishedFlowToRegularEProjectionRound241Exact as PublishedRegularE
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as RegularEPredicate
import DASHI.Physics.YangMills.BalabanCMP119RawActiveRegularEDecoderRound248Exact as RegularEDecoder
import DASHI.Physics.YangMills.BalabanPublishedUVStabilityNonlinearRGCoreExact as PublishedRG
import DASHI.Physics.Closure.YMBTToFourDimensionalContinuumRouteBoundary as ContinuumBoundary
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as DensityDictionary
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as Measure
import DASHI.Physics.YangMills.BalabanLiteralFiniteMeasureStressLaneRound125Exact as MeasureStress
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.BalabanPreferredRegularEFrontierRound240Exact as RegularE
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as RegularELocalization
import DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact as RegularEContinuation
import DASHI.Physics.YangMills.BalabanCompactSimpleHaarQuadraticCasimirExact as HaarCasimir
import DASHI.Physics.YangMills.BalabanCompactSimpleCasimirOrbitFactorizationExact as CasimirOrbit
import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact as CasimirClass
import DASHI.Physics.YangMills.BalabanCMP116FirstVariationStressPairingRound105Exact as Stress
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as StressCauchy
import DASHI.Physics.YangMills.BalabanStressShellEnergyToHilbertRound112Exact as StressHilbert
import DASHI.Physics.Closure.BalabanRGScaleTransferFrontierReceipt as RGFrontier
import DASHI.Physics.Closure.YMBalabanContinuumLimitReceipt as ContinuumLimit
import DASHI.Physics.Closure.YMDepthAsContinuumLimitReceipt as DepthContinuum
import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as MassGap
import DASHI.Geometry.Gauge.SUNPrimitives as SUN
import DASHI.Physics.YangMills.BalabanRGLane as LegacyRGLane
import DASHI.Physics.YangMills.YangMillsHighestAlphaGateDependencyExact as Gate
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsConstructivePathPrePostInvariantExact as Path

------------------------------------------------------------------------
-- Tag-free directional finite signature and YM/KK Hodge source bridge.
-- The selected physical observed dynamics and OS/KK same-action witness
-- remain explicit inputs, not fabricated inhabitants.
------------------------------------------------------------------------
open TSFVArrow public using
  ( earlyObserverCannotSeeFinal
  ; lateObserverCanSeeFinal
  ; earlyAndLateVisibilityDiffer
  ; futureBoundaryChangesSmoothing
  ; microscopicReversalInvolutive
  ; microscopicActionTimeReversalInvariant
  ; futureChoicesKeepSamePast
  ; futureChoicesChangeHiddenHistory
  ; futureChoicesHaveSameMicroscopicAction
  ; historyNotRecoverableFromActionAlone
  ; pastRecordCannotRecoverSelectedMicroHistory
  ; selectedTSFVPhysicalSignatureIs31
  )
open TSFVKKSameMetric public using
  ( SameMetricTSFVKK
  ; sameMetricKKSignatureFromTSFV
  ; sameMetricKKReversedCountExcluded
  ; globalStrictReversalRankImpossible
  )
open L31Probe public using
  ( calibratedProbeForcesThreePlusOne
  ; realizedDynamicsThreePlusOne
  ; threePlusOneDiffersFromOnePlusThree
  )
open YMKKHodge public using
  ( lorentzStarSquareIsNegative
  ; euclideanStarSquareIsPositive
  ; sameSourceDirectionalLorentzSignature
  ; creutzFiveEuclideanIsNotKK
  )
-- Genuine finite selected single-branch macro restoration, not a quantum
-- or same-H_OS theorem. Original Aharonov/Cohen/Gruss/Landsberger credited.
-- Source-native original two-boundary admissibility → original TSVF ABL
-- plus actual nontrivial finite tensor environmental overlap and exact
-- selected ABL normalization. Physical Hilbert/2017 gamma/OS still OPEN.
open TSVFOverlap public using
  ( rightAmplitude
  ; wrongAmplitude
  ; twoOutcomeABLNormalizes
  ; sourceMatchedOriginalABLNormalizes
  ; tensorOverlap
  ; tensorSquaredOverlapReduces
  ; actualTensorSquaredOverlapIsNineOverTwentyFivePower
  ; selectedBornMass
  ; selectedBornRightDominates
  ; oneAtMostWrongPower
  ; selectedBornDenominatorIsSum
  ; weightedBornMass
  ; weightedBornNormalizes
  ; wrongBornTailBoundCrossMultiplied
  ; zeroWrongFactorGivesZeroWrongMassCorrect
  ; admissibleDoesNotForcePositiveWeight
  ; adversarialWrongDominatesRightAtTwo
  )
-- Exact complex gamma amplitude/Born factor product using the original
-- rational Cayley-Dickson complex owner. Physical 2017 Eq25 source OPEN.
-- P01 selected original complex TSVF/ABL and P07 physical same-H OS core.
-- The all-k finite theorems and Eq.25 phase falsifier are source-written,
-- NOT a physical 2017 many-body macro reversal, OS spectrum or Clay proof.
open TSVF2017Env public using
  ( complexPowerBornIsBornPower
  ; environmentOverlapIsProductRate
  ; rightBornIsComplexGammaWeight
  ; wrongBornExact2017Factorization
  ; rightWrongBornRatioCross
  ; complexBornNonnegative
  ; rightBornNonnegative
  ; wrongBornNonnegative
  ; totalBornNonnegative
  ; selectedNumeratorsSumToSameTotal
  ; imaginaryAndUnitGammaHaveSameBornWeight
  ; imaginaryGammaIsNotUnitComplex
  )
open TSVF2017ABL public using
  ( projectorsComplete
  ; rightAfterWrongZero
  ; wrongAfterRightZero
  ; rightOriginalTransitionAmplitude
  ; wrongOriginalTransitionAmplitude
  ; originalABLTotalMatchesBornSum
  ; positiveSelectedComplexABL
  ; selectedOriginalABLContext
  ; selectedOriginalABLNormalizes
  ; selectedOriginalABLWrongIsFactorizedGammaOverlap
  ; actualComplexSelectedBidiSource
  ; originalAdmissibleRightAmplitudeIsComplexSource
  ; originalAdmissibleWrongAmplitudeIsComplexSource
  )
open TSVF2017Rate public using
  ( doublingRightVsWrongForAllK
  ; weightedDoublingBound
  ; wrongProbabilityExponentialDenominatorBound
  ; adversarialNoGammaControl
  )
-- General distinct-site complex tensor source and original ABL, plus
-- genuinely nonuniform all-site exponential robustness. The complex-to-Nat
-- calibration and selected pointer/environment dynamics remain unpaid.
open TSVFHeteroABL public using
  ( heterogeneousTensorBornFactorization
  ; homogeneousOverlapMatchesExisting
  ; homogeneousBornMatchesExisting
  ; heterogeneousWrongBornFactorization
  ; heterogeneousWrongBornNonnegative
  ; rightOriginalAmplitude
  ; wrongOriginalAmplitude
  ; originalHeterogeneousTotal
  ; positiveHeterogeneousTotal
  ; heterogeneousOriginalABLNormalizes
  ; heterogeneousOriginalABLHasCorrectBornFactor
  ; actualHeterogeneousAdmissibleSource
  ; admittedWrongHistoryAmplitudeIsProduct
  )
open TSVFHeteroRate public using
  ( heterogeneousExponentialRate
  ; weightedHeterogeneousRate
  ; heterogeneousWrongProbabilityCrossBound
  ; originalRightProductRecovered
  ; originalWrongProductRecovered
  )
-- Original selected-ABL complex site lists are now emitted by a genuine
-- certified finite controlled C^2-pointer/C^2-environment rotation. This
-- remains a finite four-complex-coordinate isometry, NOT the physical 2017
-- many-body device or a continuum strongly continuous Stone/OS Hamiltonian.
open TSVFControlled public using
  ( rotationNormScalesExactly
  ; rotationPreservesBornNorm
  ; controlledRecordPreservesFullBornNorm
  ; rightEmissionIsOriginalVacuum
  ; wrongEmissionIsControlledRotation
  ; pulseGeneratedWrongABLFactorization
  ; pulseGeneratedOriginalABLNormalizes
  ; threeFourCircleLaw
  ; threeFourPulseEmitsOriginalWrongQubit
  ; threeFourPulseOverlap
  ; threeFourPulseBornNineTwentyFifths
  )
open TSVFOSClock public using
  ( observerOSClockAllFiniteTimes
  ; observerOSAllFiniteReadouts
  ; selectedOSClockHamiltonian
  ; selectedTransferIsOfExactlyReconstructedH
  ; sameClockPhysicalMetricHas31Signature
  ; selectedObserverKetReallyIsMetricState
  ; identityEmbeddingCannotIntertwineWrongOSStep
  )
open TSVFGamma public using
  ( complexGammaBornWeightIsNormOfProduct
  ; complexConjugateBornNormInvariant
  ; gammaBornProductConjugationInvariant
  ; complexGammaProductConjugationBornInvariant
  ; imaginaryUnitGammaDoesNotChangeBornWeight
  )
open TSVFQubit public using
  ( rightProjectorIdempotent
  ; wrongProjectorIdempotent
  ; projectorsSumToIdentity
  ; rightAfterWrongZero
  ; wrongAfterRightZero
  ; excludedCannotBeJointlyAdmissible
  ; rightTransitionAmplitude
  ; wrongTransitionAmplitude
  ; rightBornNumerator
  ; wrongBornNumerator
  ; finiteMeasurementTotalPositive
  ; finiteOriginalABLContext
  ; finiteOriginalABLNormalization
  ; finiteABLRightBornPositive
  ; finiteABLWrongBornPositive
  ; selectedABLMatchesActualTensorOverlap
  ; selectedJointTSVFSource
  ; admissibleRightIsOriginalABLProjector
  ; admissibleWrongIsOriginalABLProjector
  ; selectedFiniteABLRightAtLeastWrong
  )
open TSVFMacro public using
  ( singleFaultMacroRobust
  ; twoFaultsReverseSelectedMacro
  ; twoFaultsDoNotPreserveOriginalPointer
  ; singleFaultChangesFineData
  ; noExactMicroRestorationFromMacro
  ; originalPastRecordUnchanged
  ; originalMicroHistoriesDiffer
  ; selectedBranchMacroRobust
  ; pastOnlyCannotDetermineSelectedMacroBranch
  ; reversalAndRobustMacroCoexist
  )
-- #1444@7c6b2efd finite same-source native gauge/codec/conditional Haar
-- explicitly copied into #1460. The further analysis-only moving-cutoff
-- module has no Golden --safe header and is NOT imported into this root.
open SUNVariableHaar public using
  ( periodicProductHaar
  ; periodicProductFiniteMeasure
  ; periodicProductHaarUnit
  ; periodicActualDensityStrictPositive
  ; periodicProductPartitionStrictPositive
  ; periodicProductIntegrationLaws
  ; periodicProductDensitySameObject
  ; periodicProductPartitionSameObject
  )
open SUNVariableGaugeHaar public using
  ( OriginalPeriodicGaugeVectorNaturality
  ; PeriodicPointwiseObservable
  ; periodicProductGaugeHaarInvariant
  ; periodicGibbsPointwise
  ; periodicWeightedPointwise
  ; periodicGaugeNumeratorInvariant
  ; periodicGaugeNormalizedExpectationInvariant
  )
open SUNBondCodec public using
  ( originalPositiveBondFinite
  ; originalPositiveBondDistinct
  ; originalPositiveBondCount
  ; originalSiteCountFormula
  ; originalPositiveBondCountFormula
  ; originalSideFourCountIs1024
  ; originalBondsDecodeEncodeAt
  ; originalBondsEncodePointwise
  ; originalBondsEncodeDecodeExactly
  ; encodeOriginalBonds
  ; decodeOriginalBonds
  )
open SUNConstructedGauge public using
  ( nativeDecode
  ; nativeEncode
  ; constructedOriginalPeriodicGaugeNaturality
  ; actualGaugeVectorEncoded
  ; actualGaugeVectorDecodedAt
  ; actualPeriodicProductMeasure
  ; actualPeriodicPartitionPositive
  ; actualPeriodicGaugeHaar
  ; actualPeriodicGaugeNormalized
  ; actualSixDeficitGaugeNormalized
  )
open SUNFiniteSafe public using
  ( originalGaugeDecodedAt
  ; encodeGaugeNatural
  ; vectorGaugeDecodedAt
  )

open FiveSectorBIDI public using
  ( threeToTwoExact
  ; fourToThreeExact
  ; fiveToFourExact
  ; fiveMatchesFourForcesCrossZero
  ; fourMatchesThreeForcesCrossZero
  ; threeMatchesTwoForcesCrossZero
  ; fiveDoesNotAutomaticallyMatchFour
  ; treeLevelCouplingTowerCoheres
  ; matchedFiveToTwo
  ; selectedLorentzian31FromSameMetric
  )

------------------------------------------------------------------------
-- Exact theorem-owner re-exports.
--
-- Re-export canonical owners.
-- Do not duplicate their proofs.
------------------------------------------------------------------------

open Density public using
  ( sourceCouplingIsBetaHistoryCoupling
  ; sourceSmallnessIsDerivedFromBetaHistory
  )

open CanonicalDensity public using
  ( betaHistoryGivesRepositoryCouplingCap
  ; canonicalStateRunningCouplingIsBetaHistory
  ; betaHistoryAndSourceTheoremGiveLiteralInvariantRegion
  )

open GeneratedDensity public using
  ( selectedDensityRepresentsExactBC1Potential
  ; selectedDensityRepresentsBC2InitialPotential
  )

open StressScale public using
  ( stressSelectedDensityIndexIsUnifiedActionIndex
  )

open Stress public using
  ( sourceDerivativeBelowExistingMarkedShell
  )

open StressHilbert public using
  ( stressCoefficientEnergyUniformBound
  ; stressPairingSquaredCauchyFromShellEnergy
  )

open RegularELocalization public using
  ( selectedRegularEIsLocalizedCompositeSum
  )

open BetaFloor public using
  ( universalCompactSimpleCasimirFloor
  ; universalCompactSimpleBetaFloor
  ; classificationAdjointCasimirAtLeastTwo
  ; classificationGroupUniversalCoefficientAtLeastElevenTwelfths
  ; uniformRemainderBelowEveryCompactSimpleCoefficient
  )

------------------------------------------------------------------------
-- Reused proof levels.
------------------------------------------------------------------------

balabanScaleDensityFlowLevel : ProofLevel
balabanScaleDensityFlowLevel =
  Density.balabanBetaDrivenSourceFlowLevel

balabanCompleteDensitySourceShapeLevel : ProofLevel
balabanCompleteDensitySourceShapeLevel =
  DensityDictionary.cmp119Section2CompleteDensitySourceShapeLevel

balabanCompleteDensityDerivedSummaryLevel : ProofLevel
balabanCompleteDensityDerivedSummaryLevel =
  DensityDictionary.cmp119Section2DerivedSummarySameObjectLevel

balabanCompleteDensityPhysicalProjectionBoundsLevel : ProofLevel
balabanCompleteDensityPhysicalProjectionBoundsLevel =
  DensityDictionary.cmp119Section2PhysicalProjectionBoundsLevel

balabanGeneratedActionDensityCompilerLevel : ProofLevel
balabanGeneratedActionDensityCompilerLevel =
  GeneratedDensity.unifiedGeneratedActionDensityCompilerLevel

balabanLiteralGeneratedActionDensityLevel : ProofLevel
balabanLiteralGeneratedActionDensityLevel =
  GeneratedDensity.literalUnifiedGeneratedActionDensityLevel

balabanCombinedRGEffectiveActionCompilerLevel : ProofLevel
balabanCombinedRGEffectiveActionCompilerLevel =
  CombinedAction.completeDensityEffectiveActionRealizationCompilerLevel

balabanLiteralCombinedRGEffectiveActionLevel : ProofLevel
balabanLiteralCombinedRGEffectiveActionLevel =
  CombinedAction.literalCompleteDensityEffectiveActionRealizationLevel

balabanGeneratedActionStressScaleCompilerLevel : ProofLevel
balabanGeneratedActionStressScaleCompilerLevel =
  StressScale.unifiedGeneratedActionStressScaleCompilerLevel

balabanLiteralGeneratedActionStressScaleLevel : ProofLevel
balabanLiteralGeneratedActionStressScaleLevel =
  StressScale.literalUnifiedGeneratedActionStressScaleLevel

balabanPublishedFlowRegularEProjectionCompilerLevel : ProofLevel
balabanPublishedFlowRegularEProjectionCompilerLevel =
  PublishedRegularE.publishedFlowToRegularEProjectionCompilerLevel

balabanRegularESection2PredicateCompilerLevel : ProofLevel
balabanRegularESection2PredicateCompilerLevel =
  RegularEPredicate.regularESection2PredicateCompilerLevel

balabanConcreteRegularELocalizationWitnessLevel : ProofLevel
balabanConcreteRegularELocalizationWitnessLevel =
  RegularEDecoder.literalCMP122Theorem1OnConcreteELocalizationPredicateLevel

balabanPublishedNonlinearRGCoreLevel : ProofLevel
balabanPublishedNonlinearRGCoreLevel =
  PublishedRG.publishedFourDimensionalNonlinearRGCoreLevel

balabanPublishedRGPhysicalSameObjectLevel : ProofLevel
balabanPublishedRGPhysicalSameObjectLevel =
  PublishedRG.literalPhysicalStateToPublishedRGCarrierLevel

balabanScaleDensityFiniteMeasureWeldLevel : ProofLevel
balabanScaleDensityFiniteMeasureWeldLevel =
  Measure.balabanDensityLiteralFiniteMeasureCompilerLevel

balabanScaleDensityStressLaneCompilerLevel : ProofLevel
balabanScaleDensityStressLaneCompilerLevel =
  MeasureStress.literalFiniteMeasureStressLaneCompilerLevel

balabanDensityAnchoredStressLaneCompilerLevel : ProofLevel
balabanDensityAnchoredStressLaneCompilerLevel =
  StressLane.densityAnchoredCanonicalMetricStressLaneCompilerLevel

balabanLiteralDensityAnchoredStressLaneInstantiationLevel : ProofLevel
balabanLiteralDensityAnchoredStressLaneInstantiationLevel =
  StressLane.literalDensityAnchoredStressLaneInstantiationLevel

balabanRegularESelectedDensityCompilerLevel : ProofLevel
balabanRegularESelectedDensityCompilerLevel =
  RegularE.regularESourceProjectionLevel

balabanRegularELocalizationSourceLevel : ProofLevel
balabanRegularELocalizationSourceLevel =
  RegularELocalization.cmp119RegularELocalizationSourceLevel

balabanRegularELocalizationCarrierLevel : ProofLevel
balabanRegularELocalizationCarrierLevel =
  RegularELocalization.literalCMP119RegularELocalizationCarrierLevel

balabanRegularEContinuationCompilerLevel : ProofLevel
balabanRegularEContinuationCompilerLevel =
  RegularEContinuation.theorem1RegularEContinuationCompilerLevel

balabanHaarCasimirCoefficientLevel : ProofLevel
balabanHaarCasimirCoefficientLevel =
  HaarCasimir.classifiedHaarQuadraticCoefficientLevel

balabanCasimirOrbitFactorizationLevel : ProofLevel
balabanCasimirOrbitFactorizationLevel =
  CasimirOrbit.compactSimpleCasimirOrbitFactorizationLevel

balabanCasimirLowerBoundTransportLevel : ProofLevel
balabanCasimirLowerBoundTransportLevel =
  CasimirOrbit.compactSimpleCasimirLowerBoundTransportLevel

balabanLiteralCasimirFactorizationLevel : ProofLevel
balabanLiteralCasimirFactorizationLevel =
  CasimirOrbit.literalWilsonGhostHaarCasimirFactorizationLevel

balabanClassifiedCasimirPositivityLevel : ProofLevel
balabanClassifiedCasimirPositivityLevel =
  CasimirClass.classificationAdjointCasimirStrictPositivityLevel

balabanStressMarkedShellReuseLevel : ProofLevel
balabanStressMarkedShellReuseLevel =
  Stress.cmp116StressReusesFirstGradientMarkedShellLevel

balabanStressPairingPhysicalWeldLevel : ProofLevel
balabanStressPairingPhysicalWeldLevel =
  Stress.literalCMP116FirstVariationStressPairingLevel

balabanStressCauchyModulusCompilerLevel : ProofLevel
balabanStressCauchyModulusCompilerLevel =
  StressCauchy.stressResponseCauchyModulusCompilerLevel

balabanStressCauchyPhysicalInsertionLevel : ProofLevel
balabanStressCauchyPhysicalInsertionLevel =
  StressCauchy.literalStressInsertionIsCMP119LocalInsertionLevel

balabanStressHilbertBoundCompilerLevel : ProofLevel
balabanStressHilbertBoundCompilerLevel =
  StressHilbert.stressShellEnergyToHilbertCompilerLevel

balabanStressHilbertPhysicalShellLevel : ProofLevel
balabanStressHilbertPhysicalShellLevel =
  StressHilbert.literalStressCoefficientEnergyIsShellPrefixLevel

------------------------------------------------------------------------
-- Exact fail-closed RG and continuum boundaries.
------------------------------------------------------------------------

balabanPublishedRGContinuumTransferOpenFlag : Bool
balabanPublishedRGContinuumTransferOpenFlag =
  ContinuumBoundary.flat4DContinuumTransferProvedHere

balabanPublishedRGContinuumTransferStillOpen :
  balabanPublishedRGContinuumTransferOpenFlag ≡ false
balabanPublishedRGContinuumTransferStillOpen =
  ContinuumBoundary.flat4DContinuumTransferProvedHereIsFalse

balabanOSWightmanContinuumConstructionOpenFlag : Bool
balabanOSWightmanContinuumConstructionOpenFlag =
  ContinuumBoundary.osWightmanContinuumConstructionProvedHere

balabanOSWightmanContinuumConstructionStillOpen :
  balabanOSWightmanContinuumConstructionOpenFlag ≡ false
balabanOSWightmanContinuumConstructionStillOpen =
  ContinuumBoundary.osWightmanContinuumConstructionProvedHereIsFalse

balabanContinuumRouteMassGapPromotionOpenFlag : Bool
balabanContinuumRouteMassGapPromotionOpenFlag =
  ContinuumBoundary.continuumMassGapPromoted

balabanContinuumRouteMassGapPromotionStillOpen :
  balabanContinuumRouteMassGapPromotionOpenFlag ≡ false
balabanContinuumRouteMassGapPromotionStillOpen =
  ContinuumBoundary.continuumMassGapPromotedIsFalse

balabanTerminalPromotionOpenFlag : Bool
balabanTerminalPromotionOpenFlag =
  ContinuumBoundary.terminalPromotion

balabanTerminalPromotionStillOpen :
  balabanTerminalPromotionOpenFlag ≡ false
balabanTerminalPromotionStillOpen =
  ContinuumBoundary.terminalPromotionIsFalse

balabanRGBlockSpinTransferOpenFlag : Bool
balabanRGBlockSpinTransferOpenFlag =
  RGFrontier.balabanBlockSpinTransferProved
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt

balabanRGContinuumConstructionOpenFlag : Bool
balabanRGContinuumConstructionOpenFlag =
  RGFrontier.continuumYangMillsConstructedHere
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt

balabanRGUniformKPAbsorptionOpenFlag : Bool
balabanRGUniformKPAbsorptionOpenFlag =
  RGFrontier.uniformKPAbsorptionThroughBalabanInductionProved
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt

balabanRGContinuumMassGapOpenFlag : Bool
balabanRGContinuumMassGapOpenFlag =
  MassGap.continuumMassGapProvedInDASHI
    (RGFrontier.balabanMassGapSurface
      RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt)

balabanRGClayPromotionFlag : Bool
balabanRGClayPromotionFlag =
  RGFrontier.clayYangMillsPromoted
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt

balabanRGUniformKPAbsorptionStillOpen :
  balabanRGUniformKPAbsorptionOpenFlag ≡ false
balabanRGUniformKPAbsorptionStillOpen =
  RGFrontier.uniformKPAbsorptionThroughBalabanInductionProvedIsFalse
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt

balabanRGBlockSpinTransferStillOpen :
  balabanRGBlockSpinTransferOpenFlag ≡ false
balabanRGBlockSpinTransferStillOpen =
  RGFrontier.canonicalBalabanRGScaleTransferBlockSpinStillOpen

balabanRGContinuumConstructionStillOpen :
  balabanRGContinuumConstructionOpenFlag ≡ false
balabanRGContinuumConstructionStillOpen =
  RGFrontier.continuumYangMillsConstructedHereIsFalse
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt

balabanRGContinuumMassGapStillOpen :
  balabanRGContinuumMassGapOpenFlag ≡ false
balabanRGContinuumMassGapStillOpen =
  RGFrontier.balabanContinuumMassGapStillFalse
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt

balabanRGClayPromotionStillFalse :
  balabanRGClayPromotionFlag ≡ false
balabanRGClayPromotionStillFalse =
  RGFrontier.canonicalBalabanRGScaleTransferNoClayPromotion

legacyBalabanLaneAlsoDeclaresNoClayPromotion :
  SUN.clayYangMillsPromoted ≡ false
legacyBalabanLaneAlsoDeclaresNoClayPromotion =
  LegacyRGLane.noClayPromotion LegacyRGLane.canonicalBalabanRGLane

------------------------------------------------------------------------
-- Reused typed continuum and RG-flow non-promotion owners.
--
-- The constructorless promotion types remain owned by their source receipts.
------------------------------------------------------------------------

BalabanContinuumLimitReceipt : Setω
BalabanContinuumLimitReceipt =
  ContinuumLimit.YMBalabanContinuumLimitReceipt

BalabanContinuumLimitPromotion : Set
BalabanContinuumLimitPromotion =
  ContinuumLimit.YMBalabanContinuumLimitPromotion

balabanContinuumLimitPromotionImpossible :
  BalabanContinuumLimitPromotion → ⊥
balabanContinuumLimitPromotionImpossible =
  ContinuumLimit.ymBalabanContinuumLimitPromotionImpossibleHere

DepthContinuumLimitReceipt : Setω
DepthContinuumLimitReceipt =
  DepthContinuum.YMDepthAsContinuumLimitReceipt

DepthContinuumLimitPromotion : Set
DepthContinuumLimitPromotion =
  DepthContinuum.YMDepthContinuumLimitPromotion

depthContinuumLimitPromotionImpossible :
  DepthContinuumLimitPromotion → ⊥
depthContinuumLimitPromotionImpossible =
  DepthContinuum.ymDepthContinuumLimitPromotionImpossibleHere

balabanContinuumLimitReceipt :
  BalabanContinuumLimitReceipt
balabanContinuumLimitReceipt =
  ContinuumLimit.canonicalYMBalabanContinuumLimitReceipt

depthContinuumLimitReceipt :
  DepthContinuumLimitReceipt
depthContinuumLimitReceipt =
  DepthContinuum.canonicalYMDepthAsContinuumLimitReceipt

------------------------------------------------------------------------
-- Normalize authority on the stricter frontier.
------------------------------------------------------------------------

data BalabanTOEAuthority : Set where
  strictScaleTransferFrontier : BalabanTOEAuthority

canonicalBalabanTOEAuthority : BalabanTOEAuthority
canonicalBalabanTOEAuthority = strictScaleTransferFrontier

legacyFullCertificateIsNotTOEPromotionAuthority : Bool
legacyFullCertificateIsNotTOEPromotionAuthority = true

legacyFullCertificateIsNotTOEPromotionAuthorityIsTrue :
  legacyFullCertificateIsNotTOEPromotionAuthority ≡ true
legacyFullCertificateIsNotTOEPromotionAuthorityIsTrue = refl

------------------------------------------------------------------------
-- Canonical normalized receipt.
------------------------------------------------------------------------

record BalabanRGTOEReceipt : Set where
  field
    scaleDensityFlow : ProofLevel
    completeDensitySourceShape : ProofLevel
    completeDensityDerivedSummary : ProofLevel
    completeDensityPhysicalProjectionBounds : ProofLevel
    scaleDensityFiniteMeasureWeld : ProofLevel
    generatedActionDensityCompiler : ProofLevel
    combinedRGEffectiveActionCompiler : ProofLevel
    generatedActionStressScaleCompiler : ProofLevel
    scaleDensityStressCompiler : ProofLevel
    densityAnchoredStressLaneCompiler : ProofLevel
    literalDensityAnchoredStressLaneInstantiation : ProofLevel

    publishedFlowRegularEProjectionCompiler : ProofLevel
    regularELocalizationSource : ProofLevel
    regularELocalizationCarrier : ProofLevel
    regularESection2PredicateCompiler : ProofLevel
    concreteRegularELocalizationWitness : ProofLevel
    regularEContinuationCompiler : ProofLevel

    haarCasimirCoefficient : ProofLevel
    casimirOrbitFactorization : ProofLevel
    casimirLowerBoundTransport : ProofLevel
    literalCasimirFactorization : ProofLevel
    classifiedCasimirPositivity : ProofLevel

    stressMarkedShellReuse : ProofLevel
    stressPairingPhysicalWeld : ProofLevel
    stressCauchyModulusCompiler : ProofLevel
    stressCauchyPhysicalInsertion : ProofLevel
    stressHilbertBoundCompiler : ProofLevel
    stressHilbertPhysicalShell : ProofLevel

    publishedNonlinearRGCore : ProofLevel
    publishedRGPhysicalSameObject : ProofLevel

    publishedRGContinuumTransferProved : Bool
    publishedRGContinuumTransferProvedIsFalse :
      publishedRGContinuumTransferProved ≡ false

    osWightmanContinuumConstructionProved : Bool
    osWightmanContinuumConstructionProvedIsFalse :
      osWightmanContinuumConstructionProved ≡ false

    uniformKPAbsorptionProved : Bool
    uniformKPAbsorptionProvedIsFalse :
      uniformKPAbsorptionProved ≡ false

    blockSpinTransferProved : Bool
    blockSpinTransferProvedIsFalse :
      blockSpinTransferProved ≡ false

    continuumYangMillsConstructed : Bool
    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    continuumMassGapProved : Bool
    continuumMassGapProvedIsFalse :
      continuumMassGapProved ≡ false

    terminalPromotion : Bool
    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    clayPromotion : Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

open BalabanRGTOEReceipt public

canonicalBalabanRGTOEReceipt : BalabanRGTOEReceipt
canonicalBalabanRGTOEReceipt =
  record
    { scaleDensityFlow =
        balabanScaleDensityFlowLevel
    ; completeDensitySourceShape =
        balabanCompleteDensitySourceShapeLevel
    ; completeDensityDerivedSummary =
        balabanCompleteDensityDerivedSummaryLevel
    ; completeDensityPhysicalProjectionBounds =
        balabanCompleteDensityPhysicalProjectionBoundsLevel
    ; scaleDensityFiniteMeasureWeld =
        balabanScaleDensityFiniteMeasureWeldLevel
    ; generatedActionDensityCompiler =
        balabanGeneratedActionDensityCompilerLevel
    ; combinedRGEffectiveActionCompiler =
        balabanCombinedRGEffectiveActionCompilerLevel
    ; generatedActionStressScaleCompiler =
        balabanGeneratedActionStressScaleCompilerLevel
    ; scaleDensityStressCompiler =
        balabanScaleDensityStressLaneCompilerLevel
    ; densityAnchoredStressLaneCompiler =
        balabanDensityAnchoredStressLaneCompilerLevel
    ; literalDensityAnchoredStressLaneInstantiation =
        balabanLiteralDensityAnchoredStressLaneInstantiationLevel
    ; publishedFlowRegularEProjectionCompiler =
        balabanPublishedFlowRegularEProjectionCompilerLevel
    ; regularELocalizationSource =
        balabanRegularELocalizationSourceLevel
    ; regularELocalizationCarrier =
        balabanRegularELocalizationCarrierLevel
    ; regularESection2PredicateCompiler =
        balabanRegularESection2PredicateCompilerLevel
    ; concreteRegularELocalizationWitness =
        balabanConcreteRegularELocalizationWitnessLevel
    ; regularEContinuationCompiler =
        balabanRegularEContinuationCompilerLevel
    ; haarCasimirCoefficient =
        balabanHaarCasimirCoefficientLevel
    ; casimirOrbitFactorization =
        balabanCasimirOrbitFactorizationLevel
    ; casimirLowerBoundTransport =
        balabanCasimirLowerBoundTransportLevel
    ; literalCasimirFactorization =
        balabanLiteralCasimirFactorizationLevel
    ; classifiedCasimirPositivity =
        balabanClassifiedCasimirPositivityLevel
    ; stressMarkedShellReuse =
        balabanStressMarkedShellReuseLevel
    ; stressPairingPhysicalWeld =
        balabanStressPairingPhysicalWeldLevel
    ; stressCauchyModulusCompiler =
        balabanStressCauchyModulusCompilerLevel
    ; stressCauchyPhysicalInsertion =
        balabanStressCauchyPhysicalInsertionLevel
    ; stressHilbertBoundCompiler =
        balabanStressHilbertBoundCompilerLevel
    ; stressHilbertPhysicalShell =
        balabanStressHilbertPhysicalShellLevel
    ; publishedNonlinearRGCore =
        balabanPublishedNonlinearRGCoreLevel
    ; publishedRGPhysicalSameObject =
        balabanPublishedRGPhysicalSameObjectLevel
    ; publishedRGContinuumTransferProved =
        balabanPublishedRGContinuumTransferOpenFlag
    ; publishedRGContinuumTransferProvedIsFalse =
        balabanPublishedRGContinuumTransferStillOpen
    ; osWightmanContinuumConstructionProved =
        balabanOSWightmanContinuumConstructionOpenFlag
    ; osWightmanContinuumConstructionProvedIsFalse =
        balabanOSWightmanContinuumConstructionStillOpen
    ; uniformKPAbsorptionProved =
        balabanRGUniformKPAbsorptionOpenFlag
    ; uniformKPAbsorptionProvedIsFalse =
        balabanRGUniformKPAbsorptionStillOpen
    ; blockSpinTransferProved =
        RGFrontier.balabanBlockSpinTransferProved
          RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt
    ; blockSpinTransferProvedIsFalse =
        balabanRGBlockSpinTransferStillOpen
    ; continuumYangMillsConstructed =
        RGFrontier.continuumYangMillsConstructedHere
          RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt
    ; continuumYangMillsConstructedIsFalse =
        balabanRGContinuumConstructionStillOpen
    ; continuumMassGapProved =
        MassGap.continuumMassGapProvedInDASHI
          (RGFrontier.balabanMassGapSurface
            RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt)
    ; continuumMassGapProvedIsFalse =
        balabanRGContinuumMassGapStillOpen
    ; terminalPromotion =
        balabanTerminalPromotionOpenFlag
    ; terminalPromotionIsFalse =
        balabanTerminalPromotionStillOpen
    ; clayPromotion =
        RGFrontier.clayYangMillsPromoted
          RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt
    ; clayPromotionIsFalse =
        balabanRGClayPromotionStillFalse
    }

------------------------------------------------------------------------
-- ZKP orchestration frame.
--
-- O/R/C/S/L/P/G/F are governance labels.
-- The mathematical contract reuses the existing typed gate contract.
------------------------------------------------------------------------

record BalabanTOEZKPFrame : Set where
  field
    O-organization : String
    R-request : String
    C-code : String
    S-state : String
    L-lattice : String
    P-proposal : String
    G-governance : String
    F-gap : String

    preconditions : List Path.PathClause
    postconditions : List Path.PathClause
    invariants : List Clay.ClayInvariant

open BalabanTOEZKPFrame public

canonicalBalabanTOEZKPFrame : BalabanTOEZKPFrame
canonicalBalabanTOEZKPFrame =
  record
    { O-organization =
        "DASHI TOE / Yang-Mills / Balaban RG"
    ; R-request =
        "Reuse and normalize scale densities, regular-E localization, Casimir, stress, and RG non-promotion."
    ; C-code =
        "Existing theorem owners only; no ESD edits; TOE imports are the integration point."
    ; S-state =
        "Finite and compiler results are reused. Physical localization and stress welds remain conditional. Continuum RG promotion remains false."
    ; L-lattice =
        "Finite Balaban densities and regular-E carriers feed the scale-uniform RG contract before any continuum consumer."
    ; P-proposal =
        "Use the strict scale-transfer frontier as authority. Keep the legacy RG lane as a source-intake facade."
    ; G-governance =
        "Fail closed. Preserve source authorship. Use ITIL change control, ISO 9000 evidence identity, ISO/IEC 42001 and 23894 claim limits, ISO/IEC 27001 and 27701 repository boundaries, NIST AI RMF risk gates, ISO 9241 clarity, Six Sigma deterministic checks, and C4/PlantUML import-graph discipline. This is process mapping, not standards certification."
    ; F-gap =
        "Open producers are nonperturbative block-spin transfer, uniform KP absorption, continuum construction, and mass-gap promotion."
    ; preconditions =
        Path.preconditions
          (Path.contractFor Gate.physicalUniformRGStep)
    ; postconditions =
        Path.postconditions
          (Path.contractFor Gate.physicalUniformRGStep)
    ; invariants =
        Path.invariants
          (Path.contractFor Gate.physicalUniformRGStep)
    }

------------------------------------------------------------------------
-- TOE postconditions.
------------------------------------------------------------------------

toeUsesStrictBalabanRGFrontier : Bool
toeUsesStrictBalabanRGFrontier = true

toeReusesScaleDensityOwners : Bool
toeReusesScaleDensityOwners = true

toeReusesRegularELocalizationOwners : Bool
toeReusesRegularELocalizationOwners = true

toeReusesCasimirStressOwners : Bool
toeReusesCasimirStressOwners = true

toeContinuumPromotionRemainsFalse : Bool
toeContinuumPromotionRemainsFalse = false

toeClayPromotionRemainsFalse : Bool
toeClayPromotionRemainsFalse = false

toeUsesStrictBalabanRGFrontierIsTrue :
  toeUsesStrictBalabanRGFrontier ≡ true
toeUsesStrictBalabanRGFrontierIsTrue = refl

toeReusesScaleDensityOwnersIsTrue :
  toeReusesScaleDensityOwners ≡ true
toeReusesScaleDensityOwnersIsTrue = refl

toeReusesRegularELocalizationOwnersIsTrue :
  toeReusesRegularELocalizationOwners ≡ true
toeReusesRegularELocalizationOwnersIsTrue = refl

toeReusesCasimirStressOwnersIsTrue :
  toeReusesCasimirStressOwners ≡ true
toeReusesCasimirStressOwnersIsTrue = refl

toeContinuumPromotionRemainsFalseIsFalse :
  toeContinuumPromotionRemainsFalse ≡ false
toeContinuumPromotionRemainsFalseIsFalse = refl

toeClayPromotionRemainsFalseIsFalse :
  toeClayPromotionRemainsFalse ≡ false
toeClayPromotionRemainsFalseIsFalse = refl

------------------------------------------------------------------------
-- Canonical R320/R295/R313/R296 -> R333 direct-source/OS reuse.
-- Bałaban CMP 116 (1988) is the mathematical source; DASHI owns only
-- the typed route compiler. Physical R320 and R333 inputs are not invented.
------------------------------------------------------------------------

balabanR320RouteSToOSCompilerLevel : ProofLevel
balabanR320RouteSToOSCompilerLevel =
  RouteS.routeSH1ToDirectOSCompilerLevel

balabanR320RouteSSelectedPhysicalSourceLevel : ProofLevel
balabanR320RouteSSelectedPhysicalSourceLevel =
  RouteS.routeSH1SelectedPhysicalPaymentLevel

balabanR320RouteSMagnitudeNotNewPhysical : Bool
balabanR320RouteSMagnitudeNotNewPhysical =
  RouteS.routeSH1ReusesR313MagnitudeCompiler

balabanR320RouteSNoSecondAbsoluteMagnitudeInput :
  balabanR320RouteSMagnitudeNotNewPhysical ≡ false
balabanR320RouteSNoSecondAbsoluteMagnitudeInput =
  RouteS.routeSH1ReusesR313MagnitudeCompilerIsFalse


------------------------------------------------------------------------
-- Preferred P2 bounded-observable alternative (rational SU2 trace).
-- The trace theorem is literal rational quaternion arithmetic; physical
-- Wilson/Gram interpretation is a separate conditional bridge.
------------------------------------------------------------------------

balabanRouteSP2TraceToCanonicalS2CompilerLevel : ProofLevel
balabanRouteSP2TraceToCanonicalS2CompilerLevel =
  P2Trace.rationalSU2TraceToSameAlgebraCompilerLevel

balabanRouteSP2TracePhysicalInterpretationLevel : ProofLevel
balabanRouteSP2TracePhysicalInterpretationLevel =
  P2Trace.rationalSU2TraceToGramInterpretationLevel

balabanRouteSP2TracePerLoopBoundFlag : Bool
balabanRouteSP2TracePerLoopBoundFlag =
  P2Trace.rationalSU2TraceSourcePaysLiteralLoopBoundedness

balabanRouteSP2TracePaysPerLoopBounds :
  balabanRouteSP2TracePerLoopBoundFlag ≡ true
balabanRouteSP2TracePaysPerLoopBounds =
  P2Trace.rationalSU2TraceSourcePaysLiteralLoopBoundednessIsTrue



balabanRouteSP2NativeNoExtraProduct : Bool
balabanRouteSP2NativeNoExtraProduct =
  P2Trace.nativeWilsonS2NoIndependentBoundedProductLeaf

balabanRouteSP2NativeNoExtraProductIsTrue :
  balabanRouteSP2NativeNoExtraProduct ≡ true
balabanRouteSP2NativeNoExtraProductIsTrue =
  P2Trace.nativeWilsonS2NoIndependentBoundedProductLeafIsTrue

balabanRouteSP2NativeNoDistance : Bool
balabanRouteSP2NativeNoDistance =
  P2Trace.nativeWilsonP2DoesNotNeedSupportDistance

balabanRouteSP2NativeNoDistanceIsFalse :
  balabanRouteSP2NativeNoDistance ≡ false
balabanRouteSP2NativeNoDistanceIsFalse =
  P2Trace.nativeWilsonP2DoesNotNeedSupportDistanceIsFalse

balabanRouteSP2NativeCompilerLevel : ProofLevel
balabanRouteSP2NativeCompilerLevel = P2Trace.nativeWilsonS2CompilerLevel


------------------------------------------------------------------------
-- R445 SAME marked-source moment -> native preferred physical measure
-- -> already-owned three P2 convergence limits (no second moment source).
------------------------------------------------------------------------

balabanRouteSP2R445IndependentMomentRequired : Bool
balabanRouteSP2R445IndependentMomentRequired =
  NativeP2.p2NativeIndependentMomentSelectionRequired

balabanRouteSP2R445IndependentMomentRequiredIsFalse :
  balabanRouteSP2R445IndependentMomentRequired ≡ false
balabanRouteSP2R445IndependentMomentRequiredIsFalse =
  NativeP2.p2NativeIndependentMomentSelectionRequiredIsFalse

balabanRouteSP2R445NativeCompilerLevel : ProofLevel
balabanRouteSP2R445NativeCompilerLevel =
  NativeP2.p2CanonicalMarkedSourceCompilerLevel


------------------------------------------------------------------------
-- Voyager 2026 video: use the canonical Route-S/P2 theorem owners and
-- a separate flat Euclidean R4 classical Hodge-basis donor. No Clay,
-- stochastic equilibrium or Donaldson-moduli promotion follows.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.YMClayVoyager2026CoverageExact as VoyagerCoverage
import DASHI.Physics.YangMills.YMClayVoyagerR4HodgeBasisExact as VoyagerHodge

voyager2026ChapterReceipts : List VoyagerCoverage.ChapterReceipt
voyager2026ChapterReceipts = VoyagerCoverage.chapterReceipts

voyager2026CurrentRouteSNotClay : RouteS.clayPromotion ≡ false
voyager2026CurrentRouteSNotClay = VoyagerCoverage.routeSStillNotClay

voyager2026EuclideanHodgeSquare :
  ∀ b → VoyagerHodge.euclideanHodgeStar
      (VoyagerHodge.euclideanHodgeStar b) ≡ b
voyager2026EuclideanHodgeSquare =
  VoyagerHodge.hodgeSquareOnSignedBasis


------------------------------------------------------------------------
-- 1 Nov cross-domain source-forced symmetry / dimension fork.
-- Genuine existing C3 CMP119 source owner is cited in the audit, and
-- not replaced by the new signed-axis finite C3/quarter-turn theorem.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.YMClayVoyagerImaginaryC3DimensionBidiExact as Imaginary
import DASHI.Physics.YangMills.YMClayVoyagerDimensionSignatureForkExact as Dim

voyagerImaginaryQuarterSquared :
  ∀ axis →
  Imaginary.quarterTurn (Imaginary.quarterTurn axis)
  ≡ Imaginary.axisNegation axis
voyagerImaginaryQuarterSquared =
  Imaginary.quarterTurnSquaredIsNegation

voyagerC3CannotIntertwineWithFourCycle :
  (f : Imaginary.TritPosition → Imaginary.SignedAxis2) →
  ((t : Imaginary.TritPosition) →
    f (Imaginary.rotateC3 t) ≡ Imaginary.quarterTurn (f t)) → ⊥
voyagerC3CannotIntertwineWithFourCycle =
  Imaginary.noC3ToQuarterTurnIntertwiner

voyagerPureYMFourMarginal :
  Dim.ymTwiceCouplingDimension Dim.four ≡ Dim.zero
voyagerPureYMFourMarginal =
  Dim.fourDimensionalMarginal

voyagerCreutzFiveNotKKFive :
  Dim.creutzFiveEuclideanLattice ≡ Dim.kkFourLorentzPlusCircle → ⊥
voyagerCreutzFiveNotKKFive = Dim.creutzIsNotKK

------------------------------------------------------------------------
-- Gauge- and observable-preserving selected Wilson blocking: strictly
-- conditional; the physical CMP119/R445 selection supplies the squares.
------------------------------------------------------------------------
import DASHI.Physics.YangMills.YMClayVoyagerCovariantWilsonCoarseFineBidiExact as WilsonBlock

voyagerSelectedBlockRetainsFineWilsonGaugeInvariant :
  ∀ {Fine Coarse Gauge Scalar}
    (selected : WilsonBlock.SelectedWilsonCoarseFine
      Fine Coarse Gauge Scalar)
    gauge fine →
  WilsonBlock.wilsonFine selected
    (WilsonBlock.gaugeOnFine selected gauge fine)
  ≡ WilsonBlock.wilsonFine selected fine
voyagerSelectedBlockRetainsFineWilsonGaugeInvariant =
  WilsonBlock.selectedFineWilsonGaugeInvariant


------------------------------------------------------------------------
-- 2026-11-01 actual selected finite side-four Wilson-C3 seam.
-- The same rational SU2 n=3 periodic bond carrier is now explicit.
-- These are proofs written on the physical finite lattice source, not
-- a new 369 analogy, not an infinite-volume measure/Clay promotion.
------------------------------------------------------------------------
import DASHI.Physics.YangMills.YMClaySide4SpatialC3WilsonNaturalityExact as Side4C3
import DASHI.Physics.YangMills.YMClaySide4RationalSU2C3WilsonTraceExact as RationalC3
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as NativeC3Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4PathSameObjectExact as NativePath

open Side4C3 public using
  (spatialC3ShiftForward; holonomyC3Naturality; wilsonC3Naturality)
open RationalC3 public using
  (rationalSU2Group; rationalTraceCyclic
  ; rationalTraceConjugationInvariant
  ; rationalSU2Side4WilsonC3GaugeInvariant)
open NativeC3Weld public using
  (nativeSiteIsSide4; nativePositiveBondIsSide4
  ; graphFieldFromActualNativeRationalSU2
  ; graphRoundTrip
  ; nativeRationalSU2Side4C3Wilson
  ; nativeRationalSU2Side4C3GaugeWilson
  ; nativeGraphC3Square)
open NativePath public using
  (side4CyclicSuccessorIsHodge
  ; nativePositiveStepEqualsHodge
  ; nativeGraphHolonomyEqualsExistingPathHolonomy
  ; nativeGraphWilsonEqualsExistingPathWilson)


------------------------------------------------------------------------
-- Native signed (positive and inverse) Wilson source and 16 ordered
-- plaquette sum, physical side-four C3.  The latter is not yet canonical
-- six-unordered-plaquette Gibbs/Haar finite action.
------------------------------------------------------------------------
import DASHI.Physics.YangMills.YMClayNativeRationalSU2AllSignedC3WilsonExact as AllSignedC3
import DASHI.Physics.YangMills.YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact as OrderedC3

open AllSignedC3 public using
  (c3SignedDirection; c3NativeData; c3SignedStepNaturality
  ; c3NativeSignedPathHolonomy; c3NativeSignedWilson)
open OrderedC3 public using
  (orientedOrderedPlaquetteWord; c3PlaquetteWord
  ; orderedWilsonPlaquetteC3; sumIndexC3
  ; sumSitesSpatialC3; orderedWilsonActionSpatialC3Invariant)


------------------------------------------------------------------------
-- Source six positive coordinate planes (not sixteen ordered pairs):
-- native SU2 plaquette holonomy is exactly the older signed-word Wilson.
------------------------------------------------------------------------
import DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact as SixSource

open SixSource public using
  (nativeSixPlaneBoundaryIsOrdered
  ; nativeSixPlaneHolonomyIsOrdered
  ; nativeSixPlaneTraceIsOrdered
  ; sixPlanePhysicalTraceAction
  ; nativeSixPlaneTraceSumEqualsOrderedSixSubfamily)


------------------------------------------------------------------------
-- Universal native SU2 group inverse / real Wilson orientation reversal
-- on the exact norm-one quaternion link carrier; selected lattice inverse-
-- edge endpoint identification remains a separate source theorem.
------------------------------------------------------------------------
import DASHI.Physics.YangMills.YMClayNativeRationalSU2FourFactorReversalExact as NativeReverse

open NativeReverse public using
  (forwardPlaquetteFour; reversePlaquetteFour
  ; inverseFourIsReversedPlaquette
  ; realTraceInverse; forwardReverseFourTraceSame)


------------------------------------------------------------------------
-- November source-complete six ORIGINAL positive plaquettes and native
-- R443/R445 SAME-config Set-universe weld. These are source-written
-- algebraic implications: no product Haar, R445 tail or gap constructed.
------------------------------------------------------------------------
import DASHI.Physics.YangMills.YMClayNativeSixPlaneC3SourceReductionExact as SixCut
import DASHI.Physics.YangMills.YMClayNativeSixPlaneC3ActualPhysicalSourceExact as SixActual
import DASHI.Physics.YangMills.YMClayR443NativeSixPlaneHaarNumeratorExact as R443Six
import DASHI.Physics.YangMills.YMClayR445NativeSU2R443SameObjectExact as R445Weld
import DASHI.Physics.YangMills.YMClayR443NativeSixPlaneC3SequenceLimitExact as R443Limit
import DASHI.Physics.YangMills.YMClayR443BondMarginalC3Exact as R443BondMarginal
import DASHI.Physics.YangMills.YMClayR445NativeSixDeficitUniformFiniteBoundExact as R445FiniteBound
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as SUNSigned
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as SUNGauge
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as SUNGibbs
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGaugeInvariantExact as SUNGaugeAction
import DASHI.Physics.YangMills.YMClayNativeSixPlaquetteSUNWilsonActionWeldExact as SUNCanonicalWilsonWeld
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as SUNVariable
import DASHI.Physics.YangMills.YMClaySUNMatrixSameFamilyR443R445Exact as SUNFamily
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as FiniteHaar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as OrderedHaar
import DASHI.Physics.YangMills.YMClaySUNMatrixSpatialC3RealFubiniExact as SUNRealC3
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeInversePlaquetteRealTraceExact as SUNInversePlane
import DASHI.Physics.YangMills.YMClayConstructedComplexFiniteAdjointTraceExact as SUNFiniteTrace
import DASHI.Physics.YangMills.YMClayBishopSetoidFiniteAdjointTraceExact as SUNBishopTrace
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as SUNGaugeHaar
import DASHI.Physics.YangMills.YMClaySUNProductHaarNativeGaugeR443Exact as SUNNativeGauge
import DASHI.Physics.YangMills.YMClaySUNNativeWilsonBondPointwiseExact as SUNPointwise
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicBondPointwiseExact as SUNVariablePointwise
import DASHI.Physics.YangMills.YMClaySUNNativeSetoidBondProductHaarExact as SUNSetoidHaar
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact as SUNSixC3
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as SUNHaar
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarR443NumeratorExact as SUNHaarR443
import DASHI.Physics.YangMills.YMClaySUNMatrixR445R320SameCovarianceExact as SUNCov

open SixActual public using
  (inversePositivePlaneIsSwappedWord
  ; swappedPositivePlaquetteIsInverse
  ; swappedPositivePlaquetteTrace
  ; nativeSelectedSixOrientation
  ; nativeSixPositiveWilsonActionSpatialC3)
open R443Six public using
  (NativeConfiguration; nativeSixTrace; nativeSixTraceC3
  ; NativeSixPlaneHaarBoundary; nativeSixPlaneR443
  ; nativeSixPlaneNumeratorC3Invariant)
open R445Weld public using
  (r443R445NativeConfigurationSameObject
  ; nativeR443SixPlaneR445Observable
  ; nativeR443R445FiniteCylinderLimits)
open R443Limit public using
  (nativeC3FiniteNumeratorSource
  ; nativeC3NormalizedExpectationAtEveryCutoff
  ; nativeC3SelectedSequenceLimitInvariant)


------------------------------------------------------------------------
-- Actual original native SU2 source 16ordered = 2x six positive planes
-- plus 4 identity terms/site; Wilson 1-ReTrace deficit = 2x six deficit.
-- R443 Gibbs consumes the SIX-source physical Wilson deficit, not raw trace.
------------------------------------------------------------------------
import DASHI.Physics.YangMills.YMClayNativeSixPlaneOrderedIdentityExact as SixOrdered

open SixOrdered public using
  (diagonalWordIsReverseOpposite
  ; nativeDiagonalHolonomyIdentity; nativeDiagonalTraceIsOne
  ; orderedAtIsTwiceSixPlusDiagonal
  ; orderedActionIsSixSourceTwicePlusDiagonal
  ; orderedDeficitAtIsTwiceSixDeficit
  ; sixPhysicalDeficitAction
  ; sixPhysicalDeficitActionSpatialC3)
open R443Six public using
  (nativeSixWilsonDeficit; nativeSixWilsonDeficitC3)


-- Original six-plane Wilson deficit is also exactly a R445 native observable.
open R445Weld public using (nativeR443SixDeficitR445Observable; r443SixDeficitIsNativeObservableSameObject)


-- 2 Nov: canonical import graph now exposes the *proved finite-source
-- propositions*, without changing the physical Haar/continuum/OS gates.
open R443BondMarginal public using
  (sixDeficitFactorsThroughBonds
  ; forgetC3CommutingSquare
  ; densityFactorsThroughBonds
  ; bondMarginalIntegrationLaws
  ; normalizedBondExpectationAgreement
  ; bondR431NumeratorC3)
open R445FiniteBound public using
  (nativeSixTraceLower
  ; nativeSixTraceUpper
  ; nativeSixDeficitNonnegative
  ; nativeSixDeficitAtMost3072
  ; nativeSixDeficitAbsoluteBound)


------------------------------------------------------------------------
-- 2026-11-02: REUSE THE ORIGINAL SU(N) MATRIX CARRIER, NOT RATIONAL HAAR.
-- These are source-written conditional theorem bodies, without kernel receipt.
-- The selected real physical Haar/Fubini, 1024-link codec, R445 uniform
-- continuum convergence, R320 true physical decay and R333 same-H spectral
-- gap are NOT discharged by the import graph.
------------------------------------------------------------------------

open SUNSigned public using
  (toExactSignedBondGroup
  ; sunSignedC3Holonomy
  ; sunSignedC3Wilson
  ; sunPositivePlaquetteHolonomy)
open SUNGauge public using
  (sunTraceConjugationInvariant
  ; sunOriginalPlaquetteTraceGaugeInvariant
  ; sunSideFourWilsonC3)
open SUNGibbs public using
  (nativeSUNSixWilsonDeficit
  ; nativeSUNWilsonGibbsDensity
  ; nativeSUNWilsonGibbsDensityStrictlyPositive
  ; nativeSUNFiniteGibbsMeasure)
open SUNFamily public using
  (sameOriginalFiniteMeasureFamily
  ; originalSixPartitionSameObject
  ; originalSixFiniteExpectation)
open FiniteHaar public using
  (productIntegralUnit
  ; productHaarPermutationInvariant)
open SUNHaar public using
  (nativeSUNProductIntegral
  ; nativeSUNProductIntegralSpatialC3Invariant
  ; nativeSUNProductIntegralUnit)
-- Exact same Gibbs measure: product Haar C3 + literal Wilson action -> R443/R431.
-- Remaining one-link Haar/Fubini, codec, integration laws and action C3
-- remain explicit sources; no independent whole-lattice Haar law is assumed.
-- N-link zero/linearity/scale/positivity are derived, not new premises.
open OrderedHaar public using
  (productIntegralZero
  ; productIntegralAdd
  ; productIntegralScale
  ; productIntegralPositive
  ; productIntegralStrictlyPositive)
-- Real physical-site C3 finite Fubini is now sourced from generic
-- commutative-monoid finite-Fubini, not postulated as a global action.
open SUNRealC3 public using
  (realSumSitesSpatialC3
  ; nativeSUNSixDeficitC3FromLocal
  ; nativeSUNWilsonActionC3FromLocal)
-- Original SUN inverse plaquette and six real plane C3 from one real
-- matrix trace-inversion law. Not an abstract Wilson action assumption.
-- Concrete finite complex-pair trace adjoint algebra (Bishop/real bridge pending).
-- Vendored Bishop setoid, not the legacy axiomatic real equality:
-- native ≃ adjoint real-trace invariance on finite complex matrices.
open SUNBishopTrace public using
  (bishopRealMatrixAdjointTrace
  ; bishopNormalizedRealTraceAdjoint)
open SUNFiniteTrace public using
  (realComplexMatrixAdjointTrace
  ; concreteNormalizedRealTraceAdjoint
  ; concreteSUNAdjointRealTrace)
-- Coordinatewise gauge Haar invariance is a consequence of one-link bi-invariance.
open SUNGaugeHaar public using
  (OneLinkSUNBilateralHaar
  ; gaugeOneLinkHaarInvariant
  ; gaugeBondVector
  ; productHaarNativeGaugeInvariant)
-- Native periodic BondField is a function; original Wilson/Gibbs observables
-- preserve pointwise bond equality without global function extensionality.
-- Same original periodic source, arbitrary cutoff n; Wilson/Gibbs functions
-- are extensional under pointwise bond equality without global funext.
open SUNVariablePointwise public using
  (variableOrientedLinkPointwise
  ; variableSignedPathPointwise
  ; variablePositivePlaquettePointwise
  ; variableSixWilsonDeficitPointwise
  ; variableWilsonActionPointwise
  ; variableGibbsDensityPointwise)
-- Keep the ACTUAL periodic bond function carrier. Setoid round-trip and
-- observable congruence replace overstrong whole-function equality.
open SUNSetoidHaar public using
  (SUNNativeSetoidBondCodec
  ; nativeSetoidProductHaar
  ; nativeSetoidHaarC3Invariant
  ; nativeSUNWilsonActionRespectsBondPointwise
  ; nativeSUNGibbsDensityRespectsBondPointwise
  ; nativeSUNPhysicalGibbsSetoidHaarC3)
open SUNPointwise public using
  (nativeOrientedLinkPointwise
  ; nativeSignedPathPointwise
  ; nativeSUNPositivePlaquettePointwise
  ; nativeSUNSixDeficitPointwise
  ; nativeSUNWilsonActionPointwise
  ; nativeSUNGibbsDensityPointwise)
open SUNNativeGauge public using
  (nativeGaugePhysicalIntegrationLaws
  ; nativeGaugeR443FromOneLink
  ; nativeGaugeNormalizedFromOneLink
  ; nativeProductHaarGaugeInvariant
  ; nativeGaugeWilsonGibbsR443
  ; nativeGaugeGibbsNumeratorInvariant
  ; nativeGaugeNormalizedExpectationInvariant)
open SUNInversePlane public using
  (sunSwappedPositivePlaneIsInverse
  ; sunSwappedPositivePlaneRealTrace
  ; matrixAdjointGivesSUNTraceInverse)
open SUNSixC3 public using
  (nativeSUNSixAtC3FromInverseRealTrace
  ; sixRealC3Reindex)
open SUNHaarR443 public using
  (nativeC3BoundaryFromAdjointRealTrace
  ; nativeC3BoundaryFromInverseTrace
  ; nativePhysicalIntegrationLaws
  ; nativePhysicalPartitionPositive
  ; nativeProductHaarR443
  ; nativeProductHaarNumeratorC3
  ; nativeProductHaarNormalizedC3
  ; nativeProductHaarUnitNumerator
  ; nativeNormalizedWilsonUnit)

open SUNCov public using
  (originalSUNR278FiniteSameExpectation
  ; originalSUNR278ContinuumSameLimit
  ; originalSUNRealCovarianceExtension)


-- Full source-native SU(N) Gibbs action (not just individual plaquettes)
-- is gauge-invariant under original periodic link transformation.
open SUNGaugeAction public using
  (sunTransformedPathSameSource
  ; sunPlaquetteRealTraceGaugeInvariant
  ; sunSixDeficitGaugeInvariant
  ; sunWilsonActionGaugeInvariant
  ; sunGibbsDensityGaugeInvariant)


-- Canonical owner reconciliation: the existing generic SUNWilsonAction was
-- already proved. This new bridge identifies it with the literal original
-- positive-six-plane signed Balaban source at each physical site.
open SUNCanonicalWilsonWeld public using
  (signedWordAsPath
  ; nativePositivePlaquetteIsCanonicalSUN
  ; canonicalNativeSiteSUNWilsonData
  ; canonicalNativeSUNWilsonSelectedListExact
  ; nativeSixAtSiteIsCanonicalSUNWilsonAction)


-- Variable-n original periodic SUN Wilson source: n genuinely changes the
-- four-torus, unlike a beta-only sequence on the fixed side-four source.
-- All-n local gauge invariance and n=3 source matching are proof terms,
-- but the continuous SU(N) Haar/UV-IR/CMP116/OS physical gates stay open.
open SUNCanonicalWilsonWeld public using
  (canonicalSUNSixWilsonDeficit
  ; nativeSixGlobalIsCanonicalSUNWilsonAction
  ; nativeSUNBetaActionIsCanonicalWilsonAction)
open SUNVariable public using
  (SUNPeriodicLinks
  ; periodicSUNPositivePlaquette
  ; periodicSUNSixDeficit
  ; periodicSUNSixDeficitGaugeInvariant
  ; periodicSUNWilsonActionGaugeInvariant
  ; periodicSUNGibbsDensityGaugeInvariant
  ; periodicSUNFiniteGibbsMeasure
  ; sideFourPlaquetteSameNativeHolonomy)
