module DASHI.Unified.Physics where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Physics.Closure.ClayNSProofRoadmapReceipt as NSRoadmap
import DASHI.Physics.Closure.ClayYMProofRoadmapReceipt as YMRoadmap
import DASHI.Physics.Closure.YMClayPromotionBoundary as YMBoundary
import DASHI.Unified.InvariantSpine as Spine
import DASHI.Unified.YMGoal1TOECompatibilityExact as YMGoal1TOE
import DASHI.Unified.BalabanRGTOERegression as BalabanRGTOE
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as YMMaxCut
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

-- Current-master R485/R546/R558 Goal-1/Pareto normalization.
-- The imported source owners remain theorem authority.
open YMMaxCut public

navierStokesObject : Spine.UnifiedObjectInvariant
navierStokesObject =
  Spine.unifiedObjectInvariant
    "navier-stokes-approach-parent"
    Unified.physicsLane
    "Navier-Stokes carrier and roadmap observations"
    "flow/PDE carrier -> approach lane -> blocked external theorem promotion"
    Unified.flowCarrier
    (Spine.defaultRoleVector "navier-stokes-approach-parent")
    Residual.partial
    Asserted.approachingClosedProof
    Spine.blockedInvariant
    (Spine.blockedJProjection "Navier-Stokes has no inhabited modular-j proof bridge")
    (Spine.blockedFormalProjectionBundle "Navier-Stokes projections are present as blocked non-promoting parent carriers")

yangMillsObject : Spine.UnifiedObjectInvariant
yangMillsObject =
  Spine.unifiedObjectInvariant
    "yang-mills-approach-parent"
    Unified.physicsLane
    "Yang-Mills carrier, RG, OS/Wightman, and Clay-boundary observations"
    "gauge/QFT carrier -> approach lane -> blocked external theorem promotion"
    Unified.gaugeCarrier
    (Spine.defaultRoleVector "yang-mills-approach-parent")
    Residual.partial
    Asserted.approachingClosedProof
    Spine.blockedInvariant
    (Spine.blockedJProjection "Yang-Mills has no inhabited modular-j proof bridge")
    (Spine.blockedFormalProjectionBundle "Yang-Mills projections are present as blocked non-promoting parent carriers")

canonicalPhysicsObjects : List Spine.UnifiedObjectInvariant
canonicalPhysicsObjects =
  navierStokesObject ∷ yangMillsObject ∷ []

navierStokesJPromotionBlocked :
  Spine.objectExternalJPromotion navierStokesObject ≡ false
navierStokesJPromotionBlocked =
  refl

yangMillsJPromotionBlocked :
  Spine.objectExternalJPromotion yangMillsObject ≡ false
yangMillsJPromotionBlocked =
  refl

navierStokesPostureIsApproaching :
  Spine.proofPosture navierStokesObject ≡ Asserted.approachingClosedProof
navierStokesPostureIsApproaching =
  refl

yangMillsPostureIsApproaching :
  Spine.proofPosture yangMillsObject ≡ Asserted.approachingClosedProof
yangMillsPostureIsApproaching =
  refl


------------------------------------------------------------------------
-- Canonical Yang-Mills Goal-1 TOE facade.
-- Proof ownership remains in the imported Yang-Mills owners.
------------------------------------------------------------------------

yangMillsGoal1PreferredVariableDomainBSourceLevel : ProofLevel
yangMillsGoal1PreferredVariableDomainBSourceLevel =
  YMGoal1TOE.goal1PreferredVariableDomainBSourceLevel

yangMillsGoal1FiniteA1WilsonActionInvarianceLevel : ProofLevel
yangMillsGoal1FiniteA1WilsonActionInvarianceLevel =
  YMGoal1TOE.goal1FiniteA1WilsonActionInvarianceLevel

yangMillsGoal1FiniteA2PeterWeylWilsonIdentificationLevel : ProofLevel
yangMillsGoal1FiniteA2PeterWeylWilsonIdentificationLevel =
  YMGoal1TOE.goal1FiniteA2PeterWeylWilsonIdentificationLevel

yangMillsGoal1A3UniformCompactContainmentLevel : ProofLevel
yangMillsGoal1A3UniformCompactContainmentLevel =
  YMGoal1TOE.goal1A3UniformCompactContainmentLevel

yangMillsGoal1A4FiniteRegularityLevel : ProofLevel
yangMillsGoal1A4FiniteRegularityLevel =
  YMGoal1TOE.goal1A4FiniteRegularityLevel

yangMillsGoal1A5FiniteGrowthControlLevel : ProofLevel
yangMillsGoal1A5FiniteGrowthControlLevel =
  YMGoal1TOE.goal1A5FiniteGrowthControlLevel

yangMillsGoal1LocalQFTCSourceLevel : ProofLevel
yangMillsGoal1LocalQFTCSourceLevel =
  YMGoal1TOE.goal1LocalQFTCSourceLevel

yangMillsGoal1C3OneStepAFIdentificationLevel : ProofLevel
yangMillsGoal1C3OneStepAFIdentificationLevel =
  YMGoal1TOE.goal1C3OneStepAFIdentificationLevel

yangMillsGoal1C4SectorRecoveryCompilerLevel : ProofLevel
yangMillsGoal1C4SectorRecoveryCompilerLevel =
  YMGoal1TOE.goal1C4SectorRecoveryCompilerLevel

yangMillsGoal1SameHNontrivialityLevel : ProofLevel
yangMillsGoal1SameHNontrivialityLevel =
  YMGoal1TOE.goal1SameHNontrivialitySemanticBridgeLevel

yangMillsGoal1ContinuumStillOpen :
  YMGoal1TOE.flat4DContinuumTransferProvedHere ≡ false
yangMillsGoal1ContinuumStillOpen =
  YMGoal1TOE.flat4DContinuumTransferStillOpen

yangMillsGoal1ContinuumMassGapStillBlocked :
  YMGoal1TOE.continuumMassGapPromoted ≡ false
yangMillsGoal1ContinuumMassGapStillBlocked =
  YMGoal1TOE.continuumMassGapStillNotPromoted

yangMillsGoal1ClayStillBlocked :
  YMGoal1TOE.clayYangMillsPromoted ≡ false
yangMillsGoal1ClayStillBlocked =
  YMGoal1TOE.clayYangMillsStillNotPromoted


------------------------------------------------------------------------
-- Canonical Balaban RG TOE facade.
-- Proof ownership remains in the imported Balaban and compact-Lie owners.
------------------------------------------------------------------------

yangMillsBalabanRGReceipt : BalabanRGTOE.BalabanRGTOEReceipt
yangMillsBalabanRGReceipt =
  BalabanRGTOE.canonicalBalabanRGTOEReceipt


yangMillsBalabanScaleDensityFlowLevel : ProofLevel
yangMillsBalabanScaleDensityFlowLevel =
  BalabanRGTOE.balabanScaleDensityFlowLevel

yangMillsBalabanCompleteDensitySourceShapeLevel : ProofLevel
yangMillsBalabanCompleteDensitySourceShapeLevel =
  BalabanRGTOE.balabanCompleteDensitySourceShapeLevel

yangMillsBalabanCompleteDensityDerivedSummaryLevel : ProofLevel
yangMillsBalabanCompleteDensityDerivedSummaryLevel =
  BalabanRGTOE.balabanCompleteDensityDerivedSummaryLevel

yangMillsBalabanCompleteDensityPhysicalProjectionBoundsLevel : ProofLevel
yangMillsBalabanCompleteDensityPhysicalProjectionBoundsLevel =
  BalabanRGTOE.balabanCompleteDensityPhysicalProjectionBoundsLevel

yangMillsBalabanScaleDensityFiniteMeasureWeldLevel : ProofLevel
yangMillsBalabanScaleDensityFiniteMeasureWeldLevel =
  BalabanRGTOE.balabanScaleDensityFiniteMeasureWeldLevel

yangMillsBalabanLiteralGeneratedActionDensityLevel : ProofLevel
yangMillsBalabanLiteralGeneratedActionDensityLevel =
  BalabanRGTOE.balabanLiteralGeneratedActionDensityLevel

yangMillsBalabanLiteralCombinedRGEffectiveActionLevel : ProofLevel
yangMillsBalabanLiteralCombinedRGEffectiveActionLevel =
  BalabanRGTOE.balabanLiteralCombinedRGEffectiveActionLevel

yangMillsBalabanLiteralGeneratedActionStressScaleLevel : ProofLevel
yangMillsBalabanLiteralGeneratedActionStressScaleLevel =
  BalabanRGTOE.balabanLiteralGeneratedActionStressScaleLevel

yangMillsBalabanScaleDensityStressLaneCompilerLevel : ProofLevel
yangMillsBalabanScaleDensityStressLaneCompilerLevel =
  BalabanRGTOE.balabanScaleDensityStressLaneCompilerLevel

yangMillsBalabanDensityAnchoredStressLaneCompilerLevel : ProofLevel
yangMillsBalabanDensityAnchoredStressLaneCompilerLevel =
  BalabanRGTOE.balabanDensityAnchoredStressLaneCompilerLevel

yangMillsBalabanLiteralDensityAnchoredStressLaneInstantiationLevel : ProofLevel
yangMillsBalabanLiteralDensityAnchoredStressLaneInstantiationLevel =
  BalabanRGTOE.balabanLiteralDensityAnchoredStressLaneInstantiationLevel

yangMillsBalabanRegularESelectedDensityCompilerLevel : ProofLevel
yangMillsBalabanRegularESelectedDensityCompilerLevel =
  BalabanRGTOE.balabanRegularESelectedDensityCompilerLevel

yangMillsBalabanRegularELocalizationSourceLevel : ProofLevel
yangMillsBalabanRegularELocalizationSourceLevel =
  BalabanRGTOE.balabanRegularELocalizationSourceLevel

yangMillsBalabanRegularELocalizationCarrierLevel : ProofLevel
yangMillsBalabanRegularELocalizationCarrierLevel =
  BalabanRGTOE.balabanRegularELocalizationCarrierLevel

yangMillsBalabanRegularEContinuationCompilerLevel : ProofLevel
yangMillsBalabanRegularEContinuationCompilerLevel =
  BalabanRGTOE.balabanRegularEContinuationCompilerLevel

yangMillsBalabanHaarCasimirCoefficientLevel : ProofLevel
yangMillsBalabanHaarCasimirCoefficientLevel =
  BalabanRGTOE.balabanHaarCasimirCoefficientLevel

yangMillsBalabanCasimirOrbitFactorizationLevel : ProofLevel
yangMillsBalabanCasimirOrbitFactorizationLevel =
  BalabanRGTOE.balabanCasimirOrbitFactorizationLevel

yangMillsBalabanCasimirLowerBoundTransportLevel : ProofLevel
yangMillsBalabanCasimirLowerBoundTransportLevel =
  BalabanRGTOE.balabanCasimirLowerBoundTransportLevel

yangMillsBalabanLiteralCasimirFactorizationLevel : ProofLevel
yangMillsBalabanLiteralCasimirFactorizationLevel =
  BalabanRGTOE.balabanLiteralCasimirFactorizationLevel

yangMillsBalabanClassifiedCasimirPositivityLevel : ProofLevel
yangMillsBalabanClassifiedCasimirPositivityLevel =
  BalabanRGTOE.balabanClassifiedCasimirPositivityLevel

yangMillsBalabanStressMarkedShellReuseLevel : ProofLevel
yangMillsBalabanStressMarkedShellReuseLevel =
  BalabanRGTOE.balabanStressMarkedShellReuseLevel

yangMillsBalabanStressPairingPhysicalWeldLevel : ProofLevel
yangMillsBalabanStressPairingPhysicalWeldLevel =
  BalabanRGTOE.balabanStressPairingPhysicalWeldLevel

yangMillsBalabanGeneratedActionDensityCompilerLevel : ProofLevel
yangMillsBalabanGeneratedActionDensityCompilerLevel =
  BalabanRGTOE.balabanGeneratedActionDensityCompilerLevel

yangMillsBalabanCombinedRGEffectiveActionCompilerLevel : ProofLevel
yangMillsBalabanCombinedRGEffectiveActionCompilerLevel =
  BalabanRGTOE.balabanCombinedRGEffectiveActionCompilerLevel

yangMillsBalabanGeneratedActionStressScaleCompilerLevel : ProofLevel
yangMillsBalabanGeneratedActionStressScaleCompilerLevel =
  BalabanRGTOE.balabanGeneratedActionStressScaleCompilerLevel

yangMillsBalabanPublishedFlowRegularEProjectionCompilerLevel : ProofLevel
yangMillsBalabanPublishedFlowRegularEProjectionCompilerLevel =
  BalabanRGTOE.balabanPublishedFlowRegularEProjectionCompilerLevel

yangMillsBalabanRegularESection2PredicateCompilerLevel : ProofLevel
yangMillsBalabanRegularESection2PredicateCompilerLevel =
  BalabanRGTOE.balabanRegularESection2PredicateCompilerLevel

yangMillsBalabanConcreteRegularELocalizationWitnessLevel : ProofLevel
yangMillsBalabanConcreteRegularELocalizationWitnessLevel =
  BalabanRGTOE.balabanConcreteRegularELocalizationWitnessLevel

yangMillsBalabanStressCauchyModulusCompilerLevel : ProofLevel
yangMillsBalabanStressCauchyModulusCompilerLevel =
  BalabanRGTOE.balabanStressCauchyModulusCompilerLevel

yangMillsBalabanStressCauchyPhysicalInsertionLevel : ProofLevel
yangMillsBalabanStressCauchyPhysicalInsertionLevel =
  BalabanRGTOE.balabanStressCauchyPhysicalInsertionLevel

yangMillsBalabanStressHilbertBoundCompilerLevel : ProofLevel
yangMillsBalabanStressHilbertBoundCompilerLevel =
  BalabanRGTOE.balabanStressHilbertBoundCompilerLevel

yangMillsBalabanStressHilbertPhysicalShellLevel : ProofLevel
yangMillsBalabanStressHilbertPhysicalShellLevel =
  BalabanRGTOE.balabanStressHilbertPhysicalShellLevel

yangMillsBalabanPublishedNonlinearRGCoreLevel : ProofLevel
yangMillsBalabanPublishedNonlinearRGCoreLevel =
  BalabanRGTOE.balabanPublishedNonlinearRGCoreLevel

yangMillsBalabanPublishedRGPhysicalSameObjectLevel : ProofLevel
yangMillsBalabanPublishedRGPhysicalSameObjectLevel =
  BalabanRGTOE.balabanPublishedRGPhysicalSameObjectLevel

yangMillsBalabanRGUniformKPAbsorptionStillOpen :
  BalabanRGTOE.balabanRGUniformKPAbsorptionOpenFlag ≡ false
yangMillsBalabanRGUniformKPAbsorptionStillOpen =
  BalabanRGTOE.balabanRGUniformKPAbsorptionStillOpen

yangMillsBalabanRGBlockSpinTransferStillOpen :
  BalabanRGTOE.balabanRGBlockSpinTransferOpenFlag ≡ false
yangMillsBalabanRGBlockSpinTransferStillOpen =
  BalabanRGTOE.balabanRGBlockSpinTransferStillOpen

yangMillsBalabanPublishedRGContinuumTransferStillOpen :
  BalabanRGTOE.balabanPublishedRGContinuumTransferOpenFlag ≡ false
yangMillsBalabanPublishedRGContinuumTransferStillOpen =
  BalabanRGTOE.balabanPublishedRGContinuumTransferStillOpen

yangMillsBalabanOSWightmanContinuumConstructionStillOpen :
  BalabanRGTOE.balabanOSWightmanContinuumConstructionOpenFlag ≡ false
yangMillsBalabanOSWightmanContinuumConstructionStillOpen =
  BalabanRGTOE.balabanOSWightmanContinuumConstructionStillOpen

yangMillsBalabanContinuumRouteMassGapPromotionStillOpen :
  BalabanRGTOE.balabanContinuumRouteMassGapPromotionOpenFlag ≡ false
yangMillsBalabanContinuumRouteMassGapPromotionStillOpen =
  BalabanRGTOE.balabanContinuumRouteMassGapPromotionStillOpen

yangMillsBalabanRGContinuumConstructionStillOpen :
  BalabanRGTOE.balabanRGContinuumConstructionOpenFlag ≡ false
yangMillsBalabanRGContinuumConstructionStillOpen =
  BalabanRGTOE.balabanRGContinuumConstructionStillOpen

yangMillsBalabanContinuumMassGapStillOpen :
  BalabanRGTOE.balabanRGContinuumMassGapOpenFlag ≡ false
yangMillsBalabanContinuumMassGapStillOpen =
  BalabanRGTOE.balabanRGContinuumMassGapStillOpen

yangMillsBalabanTerminalPromotionStillOpen :
  BalabanRGTOE.balabanTerminalPromotionOpenFlag ≡ false
yangMillsBalabanTerminalPromotionStillOpen =
  BalabanRGTOE.balabanTerminalPromotionStillOpen

yangMillsBalabanClayPromotionStillFalse :
  BalabanRGTOE.balabanRGClayPromotionFlag ≡ false
yangMillsBalabanClayPromotionStillFalse =
  BalabanRGTOE.balabanRGClayPromotionStillFalse


yangMillsBalabanContinuumLimitReceipt :
  BalabanRGTOE.BalabanContinuumLimitReceipt
yangMillsBalabanContinuumLimitReceipt =
  BalabanRGTOE.balabanContinuumLimitReceipt

yangMillsBalabanContinuumLimitPromotionImpossible :
  BalabanRGTOE.BalabanContinuumLimitPromotion → ⊥
yangMillsBalabanContinuumLimitPromotionImpossible =
  BalabanRGTOE.balabanContinuumLimitPromotionImpossible

yangMillsDepthContinuumLimitReceipt :
  BalabanRGTOE.DepthContinuumLimitReceipt
yangMillsDepthContinuumLimitReceipt =
  BalabanRGTOE.depthContinuumLimitReceipt

yangMillsDepthContinuumLimitPromotionImpossible :
  BalabanRGTOE.DepthContinuumLimitPromotion → ⊥
yangMillsDepthContinuumLimitPromotionImpossible =
  BalabanRGTOE.depthContinuumLimitPromotionImpossible

yangMillsGoal1ParetoZKPFrame : YMMaxCut.Goal1ParetoTOEZKPFrame
yangMillsGoal1ParetoZKPFrame = YMMaxCut.canonicalGoal1ParetoTOEZKPFrame

------------------------------------------------------------------------
-- Joint Balaban RG + R559 same-owner max-cut physics facade.
------------------------------------------------------------------------

import DASHI.Unified.BalabanR559TOEMaxCutExact as BalabanR559TOE

yangMillsBalabanR559MaxCutReceipt :
  BalabanR559TOE.BalabanR559TOEMaxCutReceipt
yangMillsBalabanR559MaxCutReceipt =
  BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

yangMillsBalabanR559PublishedContinuumStillOpen :
  BalabanR559TOE.publishedContinuumPromotion
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
yangMillsBalabanR559PublishedContinuumStillOpen =
  BalabanR559TOE.publishedContinuumPromotionIsFalse
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

yangMillsBalabanR559ContinuumMassGapStillBlocked :
  BalabanR559TOE.continuumMassGapPromotion
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
yangMillsBalabanR559ContinuumMassGapStillBlocked =
  BalabanR559TOE.continuumMassGapPromotionIsFalse
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

yangMillsBalabanR559ClayPromotionStillBlocked :
  BalabanR559TOE.clayPromotion
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt
  ≡ false
yangMillsBalabanR559ClayPromotionStillBlocked =
  BalabanR559TOE.clayPromotionIsFalse
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

yangMillsBalabanR559Gate4UnresolvedCount : ℕ
yangMillsBalabanR559Gate4UnresolvedCount =
  BalabanR559TOE.gate4UnresolvedCount
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

yangMillsBalabanR559Gate4UnresolvedCountIs58 :
  yangMillsBalabanR559Gate4UnresolvedCount ≡ 58
yangMillsBalabanR559Gate4UnresolvedCountIs58 =
  BalabanR559TOE.gate4UnresolvedCountIs58
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

yangMillsBalabanR559Gate4DefinitionLevel : ProofLevel
yangMillsBalabanR559Gate4DefinitionLevel =
  BalabanR559TOE.gate4DefinitionLevel
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

yangMillsBalabanR559Gate4InhabitantsLevel : ProofLevel
yangMillsBalabanR559Gate4InhabitantsLevel =
  BalabanR559TOE.gate4InhabitantsLevel
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

yangMillsBalabanScaleTransferNonPromotion :
  BalabanR559TOE.ScaleTransferPromotion → ⊥
yangMillsBalabanScaleTransferNonPromotion =
  BalabanR559TOE.scaleTransferPromotionEliminator
    BalabanR559TOE.canonicalBalabanR559TOEMaxCutReceipt

------------------------------------------------------------------------
-- Implement-A-to-D reuse-only Yang-Mills physics facade.
------------------------------------------------------------------------

import DASHI.Unified.YMImplementAToDTOEMaxCutExact as YMAD

yangMillsImplementAToDMaxCutReceipt :
  YMAD.YMImplementAToDTOEMaxCutReceipt
yangMillsImplementAToDMaxCutReceipt =
  YMAD.canonicalYMImplementAToDTOEMaxCutReceipt

yangMillsImplementAToDZKPFrame : YMAD.YMImplementAToDZKPFrame
yangMillsImplementAToDZKPFrame =
  YMAD.canonicalYMImplementAToDZKPFrame

yangMillsImplementAToDPublishedContinuumStillBlocked :
  YMAD.publishedContinuumPromotion YMAD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
yangMillsImplementAToDPublishedContinuumStillBlocked =
  YMAD.publishedContinuumPromotionIsFalse
    YMAD.canonicalYMImplementAToDTOEMaxCutReceipt

yangMillsImplementAToDContinuumMassGapStillBlocked :
  YMAD.continuumMassGapPromotion YMAD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
yangMillsImplementAToDContinuumMassGapStillBlocked =
  YMAD.continuumMassGapPromotionIsFalse
    YMAD.canonicalYMImplementAToDTOEMaxCutReceipt

yangMillsImplementAToDClayStillBlocked :
  YMAD.clayPromotion YMAD.canonicalYMImplementAToDTOEMaxCutReceipt
  ≡ false
yangMillsImplementAToDClayStillBlocked =
  YMAD.clayPromotionIsFalse YMAD.canonicalYMImplementAToDTOEMaxCutReceipt

yangMillsImplementAToDScaleTransferNonPromotion :
  BalabanR559TOE.ScaleTransferPromotion → ⊥
yangMillsImplementAToDScaleTransferNonPromotion =
  YMAD.scaleTransferPromotionEliminator
    YMAD.canonicalYMImplementAToDTOEMaxCutReceipt


------------------------------------------------------------------------
-- Computational-imaging observer facade.
-- Reuse the existing optics owners. Do not duplicate their proofs.
------------------------------------------------------------------------

import DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact as DiffuserImaging
import DASHI.Physics.Optics.DiffuserRedundantRecoveryExact as DiffuserRecovery
import DASHI.Physics.Optics.DiffuserNoiseStableRecoveryExact as DiffuserStability
import DASHI.Physics.Optics.FresnelZonePlateDiffuserCodecBridgeExact as ZonePlate

diffuserImagingZKPFrame :
  DiffuserImaging.DiffuserImagingTOEZKPFrame
diffuserImagingZKPFrame =
  DiffuserImaging.canonicalDiffuserImagingTOEZKPFrame

open DiffuserImaging public using
  ( DiffuserImagingTOEZKPFrame
  ; roundTripImpliesIdentifiable
  ; noUniversalDecoderAfterClip
  ; saturatedCollision
  ; overlapThenClip
  )

open DiffuserRecovery public using
  ( redundantRecovery
  ; recordedCodeInjective
  ; firstPixelOnlyCannotRecoverDepth
  ; depthRecoveryReceipt
  ; recordedCollisionWouldContradictDepth
  )

open DiffuserStability public using
  ( RestrictedInverseBudget
  ; MeasuredReconstruction
  ; stableReconstructionBound
  ; stableWithMatchedResidual
  )

open ZonePlate public using
  ( codedDepthRoundTrip
  ; noUniversalDepthDecoder
  ; noRechartRepairsSaturatedDepth
  )
