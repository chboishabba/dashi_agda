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
