module DASHI.EverythingTOESymmetryResolved369 where

import DASHI.Unified.SensibLawGovernanceTOEExact as GovernanceTOE
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary
import DASHI.Law.SensibLawAgdaFirstLegalRuntimeEverything as LegalRuntime
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false; true)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Reuse the existing exact finite GR/quantum proof-term regression.
-- It contains a terminal physical non-promotion theorem.
-- Do not replace this import with DASHI.Unifier placeholder axioms.
import DASHI.Unified.GRQuantumProofTermRegression

import DASHI.Unified.YMGoal1TOECompatibilityExact as YMGoal1TOE

-- Reuse the strict Balaban RG normalization and its fail-closed continuum boundary.
import DASHI.Unified.BalabanRGTOERegression as BalabanRGTOE
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as YMMaxCut

-- Current-master R485/R546/R558 Goal-1/Pareto normalization.
-- The imported source owners remain theorem authority.
open YMMaxCut public

open BalabanRGTOE public using
  ( sourceCouplingIsBetaHistoryCoupling
  ; sourceSmallnessIsDerivedFromBetaHistory
  ; betaHistoryGivesRepositoryCouplingCap
  ; canonicalStateRunningCouplingIsBetaHistory
  ; betaHistoryAndSourceTheoremGiveLiteralInvariantRegion
  ; selectedDensityRepresentsExactBC1Potential
  ; selectedDensityRepresentsBC2InitialPotential
  ; stressSelectedDensityIndexIsUnifiedActionIndex
  ; sourceDerivativeBelowExistingMarkedShell
  ; stressCoefficientEnergyUniformBound
  ; stressPairingSquaredCauchyFromShellEnergy
  ; selectedRegularEIsLocalizedCompositeSum
  ; universalCompactSimpleCasimirFloor
  ; universalCompactSimpleBetaFloor
  ; classificationAdjointCasimirAtLeastTwo
  ; classificationGroupUniversalCoefficientAtLeastElevenTwelfths
  ; uniformRemainderBelowEveryCompactSimpleCoefficient
  )

toeBalabanRGBlockSpinTransferStillOpen :
  BalabanRGTOE.balabanRGBlockSpinTransferOpenFlag ≡ false
toeBalabanRGBlockSpinTransferStillOpen =
  BalabanRGTOE.balabanRGBlockSpinTransferStillOpen

toeBalabanRGUniformKPAbsorptionStillOpen :
  BalabanRGTOE.balabanRGUniformKPAbsorptionOpenFlag
  ≡ false
toeBalabanRGUniformKPAbsorptionStillOpen =
  BalabanRGTOE.balabanRGUniformKPAbsorptionStillOpen

toeBalabanRGContinuumConstructionStillOpen :
  BalabanRGTOE.balabanRGContinuumConstructionOpenFlag ≡ false
toeBalabanRGContinuumConstructionStillOpen =
  BalabanRGTOE.balabanRGContinuumConstructionStillOpen

toeBalabanRGContinuumMassGapStillOpen :
  BalabanRGTOE.balabanRGContinuumMassGapOpenFlag
  ≡ false
toeBalabanRGContinuumMassGapStillOpen =
  BalabanRGTOE.balabanRGContinuumMassGapStillOpen

toeBalabanRGClayPromotionStillFalse :
  BalabanRGTOE.balabanRGClayPromotionFlag ≡ false
toeBalabanRGClayPromotionStillFalse =
  BalabanRGTOE.balabanRGClayPromotionStillFalse

toeBalabanRGZKPFrame : BalabanRGTOE.BalabanTOEZKPFrame
toeBalabanRGZKPFrame =
  BalabanRGTOE.canonicalBalabanTOEZKPFrame

toeBalabanRGReceipt : BalabanRGTOE.BalabanRGTOEReceipt
toeBalabanRGReceipt =
  BalabanRGTOE.canonicalBalabanRGTOEReceipt

------------------------------------------------------------------------
-- Normalized Balaban density, regular-E, stress, and continuum surfaces.
------------------------------------------------------------------------


toeBalabanScaleDensityFlowLevel : ProofLevel
toeBalabanScaleDensityFlowLevel =
  BalabanRGTOE.balabanScaleDensityFlowLevel

toeBalabanCompleteDensitySourceShapeLevel : ProofLevel
toeBalabanCompleteDensitySourceShapeLevel =
  BalabanRGTOE.balabanCompleteDensitySourceShapeLevel

toeBalabanCompleteDensityDerivedSummaryLevel : ProofLevel
toeBalabanCompleteDensityDerivedSummaryLevel =
  BalabanRGTOE.balabanCompleteDensityDerivedSummaryLevel

toeBalabanCompleteDensityPhysicalProjectionBoundsLevel : ProofLevel
toeBalabanCompleteDensityPhysicalProjectionBoundsLevel =
  BalabanRGTOE.balabanCompleteDensityPhysicalProjectionBoundsLevel

toeBalabanScaleDensityFiniteMeasureWeldLevel : ProofLevel
toeBalabanScaleDensityFiniteMeasureWeldLevel =
  BalabanRGTOE.balabanScaleDensityFiniteMeasureWeldLevel

toeBalabanLiteralGeneratedActionDensityLevel : ProofLevel
toeBalabanLiteralGeneratedActionDensityLevel =
  BalabanRGTOE.balabanLiteralGeneratedActionDensityLevel

toeBalabanLiteralCombinedRGEffectiveActionLevel : ProofLevel
toeBalabanLiteralCombinedRGEffectiveActionLevel =
  BalabanRGTOE.balabanLiteralCombinedRGEffectiveActionLevel

toeBalabanLiteralGeneratedActionStressScaleLevel : ProofLevel
toeBalabanLiteralGeneratedActionStressScaleLevel =
  BalabanRGTOE.balabanLiteralGeneratedActionStressScaleLevel

toeBalabanScaleDensityStressLaneCompilerLevel : ProofLevel
toeBalabanScaleDensityStressLaneCompilerLevel =
  BalabanRGTOE.balabanScaleDensityStressLaneCompilerLevel

toeBalabanDensityAnchoredStressLaneCompilerLevel : ProofLevel
toeBalabanDensityAnchoredStressLaneCompilerLevel =
  BalabanRGTOE.balabanDensityAnchoredStressLaneCompilerLevel

toeBalabanLiteralDensityAnchoredStressLaneInstantiationLevel : ProofLevel
toeBalabanLiteralDensityAnchoredStressLaneInstantiationLevel =
  BalabanRGTOE.balabanLiteralDensityAnchoredStressLaneInstantiationLevel

toeBalabanGeneratedActionDensityCompilerLevel : ProofLevel
toeBalabanGeneratedActionDensityCompilerLevel =
  BalabanRGTOE.balabanGeneratedActionDensityCompilerLevel

toeBalabanCombinedRGEffectiveActionCompilerLevel : ProofLevel
toeBalabanCombinedRGEffectiveActionCompilerLevel =
  BalabanRGTOE.balabanCombinedRGEffectiveActionCompilerLevel

toeBalabanGeneratedActionStressScaleCompilerLevel : ProofLevel
toeBalabanGeneratedActionStressScaleCompilerLevel =
  BalabanRGTOE.balabanGeneratedActionStressScaleCompilerLevel

toeBalabanStressCauchyModulusCompilerLevel : ProofLevel
toeBalabanStressCauchyModulusCompilerLevel =
  BalabanRGTOE.balabanStressCauchyModulusCompilerLevel

toeBalabanStressCauchyPhysicalInsertionLevel : ProofLevel
toeBalabanStressCauchyPhysicalInsertionLevel =
  BalabanRGTOE.balabanStressCauchyPhysicalInsertionLevel

toeBalabanStressHilbertBoundCompilerLevel : ProofLevel
toeBalabanStressHilbertBoundCompilerLevel =
  BalabanRGTOE.balabanStressHilbertBoundCompilerLevel

toeBalabanStressHilbertPhysicalShellLevel : ProofLevel
toeBalabanStressHilbertPhysicalShellLevel =
  BalabanRGTOE.balabanStressHilbertPhysicalShellLevel

toeBalabanPublishedFlowRegularEProjectionCompilerLevel : ProofLevel
toeBalabanPublishedFlowRegularEProjectionCompilerLevel =
  BalabanRGTOE.balabanPublishedFlowRegularEProjectionCompilerLevel

toeBalabanRegularESection2PredicateCompilerLevel : ProofLevel
toeBalabanRegularESection2PredicateCompilerLevel =
  BalabanRGTOE.balabanRegularESection2PredicateCompilerLevel

toeBalabanConcreteRegularELocalizationWitnessLevel : ProofLevel
toeBalabanConcreteRegularELocalizationWitnessLevel =
  BalabanRGTOE.balabanConcreteRegularELocalizationWitnessLevel


toeBalabanRegularESelectedDensityCompilerLevel : ProofLevel
toeBalabanRegularESelectedDensityCompilerLevel =
  BalabanRGTOE.balabanRegularESelectedDensityCompilerLevel

toeBalabanRegularELocalizationSourceLevel : ProofLevel
toeBalabanRegularELocalizationSourceLevel =
  BalabanRGTOE.balabanRegularELocalizationSourceLevel

toeBalabanRegularELocalizationCarrierLevel : ProofLevel
toeBalabanRegularELocalizationCarrierLevel =
  BalabanRGTOE.balabanRegularELocalizationCarrierLevel

toeBalabanRegularEContinuationCompilerLevel : ProofLevel
toeBalabanRegularEContinuationCompilerLevel =
  BalabanRGTOE.balabanRegularEContinuationCompilerLevel

toeBalabanHaarCasimirCoefficientLevel : ProofLevel
toeBalabanHaarCasimirCoefficientLevel =
  BalabanRGTOE.balabanHaarCasimirCoefficientLevel

toeBalabanCasimirOrbitFactorizationLevel : ProofLevel
toeBalabanCasimirOrbitFactorizationLevel =
  BalabanRGTOE.balabanCasimirOrbitFactorizationLevel

toeBalabanCasimirLowerBoundTransportLevel : ProofLevel
toeBalabanCasimirLowerBoundTransportLevel =
  BalabanRGTOE.balabanCasimirLowerBoundTransportLevel

toeBalabanLiteralCasimirFactorizationLevel : ProofLevel
toeBalabanLiteralCasimirFactorizationLevel =
  BalabanRGTOE.balabanLiteralCasimirFactorizationLevel

toeBalabanClassifiedCasimirPositivityLevel : ProofLevel
toeBalabanClassifiedCasimirPositivityLevel =
  BalabanRGTOE.balabanClassifiedCasimirPositivityLevel

toeBalabanStressMarkedShellReuseLevel : ProofLevel
toeBalabanStressMarkedShellReuseLevel =
  BalabanRGTOE.balabanStressMarkedShellReuseLevel

toeBalabanStressPairingPhysicalWeldLevel : ProofLevel
toeBalabanStressPairingPhysicalWeldLevel =
  BalabanRGTOE.balabanStressPairingPhysicalWeldLevel

toeBalabanPublishedNonlinearRGCoreLevel : ProofLevel
toeBalabanPublishedNonlinearRGCoreLevel =
  BalabanRGTOE.balabanPublishedNonlinearRGCoreLevel

toeBalabanPublishedRGPhysicalSameObjectLevel : ProofLevel
toeBalabanPublishedRGPhysicalSameObjectLevel =
  BalabanRGTOE.balabanPublishedRGPhysicalSameObjectLevel

toeBalabanPublishedRGContinuumTransferStillOpen :
  BalabanRGTOE.balabanPublishedRGContinuumTransferOpenFlag ≡ false
toeBalabanPublishedRGContinuumTransferStillOpen =
  BalabanRGTOE.balabanPublishedRGContinuumTransferStillOpen

toeBalabanOSWightmanContinuumConstructionStillOpen :
  BalabanRGTOE.balabanOSWightmanContinuumConstructionOpenFlag ≡ false
toeBalabanOSWightmanContinuumConstructionStillOpen =
  BalabanRGTOE.balabanOSWightmanContinuumConstructionStillOpen

toeBalabanContinuumRouteMassGapPromotionStillOpen :
  BalabanRGTOE.balabanContinuumRouteMassGapPromotionOpenFlag ≡ false
toeBalabanContinuumRouteMassGapPromotionStillOpen =
  BalabanRGTOE.balabanContinuumRouteMassGapPromotionStillOpen

toeBalabanTerminalPromotionStillOpen :
  BalabanRGTOE.balabanTerminalPromotionOpenFlag ≡ false
toeBalabanTerminalPromotionStillOpen =
  BalabanRGTOE.balabanTerminalPromotionStillOpen

------------------------------------------------------------------------
-- Current-branch Yang-Mills Goal-1 compatibility exports.
-- The theorem owners remain R435--R439 and the closure boundaries.
------------------------------------------------------------------------

toe369YangMillsGoal1FiniteASourceLevel : ProofLevel
toe369YangMillsGoal1FiniteASourceLevel =
  YMGoal1TOE.goal1FiniteASourceLevel

toe369YangMillsGoal1CanonicalSelectedBSourceLevel : ProofLevel
toe369YangMillsGoal1CanonicalSelectedBSourceLevel =
  YMGoal1TOE.goal1CanonicalSelectedBSourceLevel

toe369YangMillsGoal1LiteralCMP116RateSourceLevel : ProofLevel
toe369YangMillsGoal1LiteralCMP116RateSourceLevel =
  YMGoal1TOE.goal1LiteralCMP116RateSourceLevel

toe369YangMillsGoal1LocalQFTCSourceLevel : ProofLevel
toe369YangMillsGoal1LocalQFTCSourceLevel =
  YMGoal1TOE.goal1LocalQFTCSourceLevel

toe369YangMillsGoal1SameHNontrivialityLevel : ProofLevel
toe369YangMillsGoal1SameHNontrivialityLevel =
  YMGoal1TOE.goal1SameHNontrivialitySemanticBridgeLevel

toe369YangMillsFlat4DContinuumStillOpen :
  YMGoal1TOE.flat4DContinuumTransferProvedHere ≡ false
toe369YangMillsFlat4DContinuumStillOpen =
  YMGoal1TOE.flat4DContinuumTransferStillOpen

toe369YangMillsContinuumMassGapStillNotPromoted :
  YMGoal1TOE.continuumMassGapPromoted ≡ false
toe369YangMillsContinuumMassGapStillNotPromoted =
  YMGoal1TOE.continuumMassGapStillNotPromoted

toe369YangMillsClayStillNotPromoted :
  YMGoal1TOE.clayYangMillsPromoted ≡ false
toe369YangMillsClayStillNotPromoted =
  YMGoal1TOE.clayYangMillsStillNotPromoted

toe369YangMillsGoal1ZKPFrame : YMGoal1TOE.YMGoal1TOEZKPFrame
toe369YangMillsGoal1ZKPFrame =
  YMGoal1TOE.canonicalYMGoal1TOEZKPFrame


------------------------------------------------------------------------
-- Preferred R440--R444 Goal-1 source cuts.
------------------------------------------------------------------------

toe369YangMillsGoal1FiniteA1WilsonActionInvarianceLevel : ProofLevel
toe369YangMillsGoal1FiniteA1WilsonActionInvarianceLevel =
  YMGoal1TOE.goal1FiniteA1WilsonActionInvarianceLevel

toe369YangMillsGoal1FiniteA1ProductHaarInvarianceLevel : ProofLevel
toe369YangMillsGoal1FiniteA1ProductHaarInvarianceLevel =
  YMGoal1TOE.goal1FiniteA1ProductHaarInvarianceLevel

toe369YangMillsGoal1FiniteA1DensityInvariantCompilerLevel : ProofLevel
toe369YangMillsGoal1FiniteA1DensityInvariantCompilerLevel =
  YMGoal1TOE.goal1FiniteA1DensityInvariantCompilerLevel

toe369YangMillsGoal1FiniteA2PeterWeylWilsonIdentificationLevel : ProofLevel
toe369YangMillsGoal1FiniteA2PeterWeylWilsonIdentificationLevel =
  YMGoal1TOE.goal1FiniteA2PeterWeylWilsonIdentificationLevel

toe369YangMillsGoal1FiniteA2SquareCompilerLevel : ProofLevel
toe369YangMillsGoal1FiniteA2SquareCompilerLevel =
  YMGoal1TOE.goal1FiniteA2SquareCompilerLevel

toe369YangMillsGoal1PreferredVariableDomainBSourceLevel : ProofLevel
toe369YangMillsGoal1PreferredVariableDomainBSourceLevel =
  YMGoal1TOE.goal1PreferredVariableDomainBSourceLevel

toe369YangMillsGoal1R429RootedTraceEncodingLevel : ProofLevel
toe369YangMillsGoal1R429RootedTraceEncodingLevel =
  YMGoal1TOE.goal1R429RootedTraceEncodingLevel

toe369YangMillsGoal1R429RootedTraceCountCompilerLevel : ProofLevel
toe369YangMillsGoal1R429RootedTraceCountCompilerLevel =
  YMGoal1TOE.goal1R429RootedTraceCountCompilerLevel

toe369YangMillsGoal1R429SourceDecayReserveLevel : ProofLevel
toe369YangMillsGoal1R429SourceDecayReserveLevel =
  YMGoal1TOE.goal1R429SourceDecayReserveLevel

toe369YangMillsGoal1R429EntropyBudgetCompilerLevel : ProofLevel
toe369YangMillsGoal1R429EntropyBudgetCompilerLevel =
  YMGoal1TOE.goal1R429EntropyBudgetCompilerLevel

toe369YangMillsGoal1LegacyGlobalTreeMetricNotPreferred :
  YMGoal1TOE.legacyGlobalTreeMetricPreferred ≡ false
toe369YangMillsGoal1LegacyGlobalTreeMetricNotPreferred =
  YMGoal1TOE.legacyGlobalTreeMetricPreferredIsFalse


------------------------------------------------------------------------
-- Reused A3/A4/A5 and C3/C4 canonical owner exports.
------------------------------------------------------------------------

toe369YangMillsGoal1A3UniformCompactContainmentLevel : ProofLevel
toe369YangMillsGoal1A3UniformCompactContainmentLevel =
  YMGoal1TOE.goal1A3UniformCompactContainmentLevel

toe369YangMillsGoal1A3ExtractedClusterCylinderAgreementLevel : ProofLevel
toe369YangMillsGoal1A3ExtractedClusterCylinderAgreementLevel =
  YMGoal1TOE.goal1A3ExtractedClusterCylinderAgreementLevel

toe369YangMillsGoal1A3TightnessSubsequenceCompilerLevel : ProofLevel
toe369YangMillsGoal1A3TightnessSubsequenceCompilerLevel =
  YMGoal1TOE.goal1A3TightnessSubsequenceCompilerLevel

toe369YangMillsGoal1A4FiniteRegularityLevel : ProofLevel
toe369YangMillsGoal1A4FiniteRegularityLevel =
  YMGoal1TOE.goal1A4FiniteRegularityLevel

toe369YangMillsGoal1A5FiniteGrowthControlLevel : ProofLevel
toe369YangMillsGoal1A5FiniteGrowthControlLevel =
  YMGoal1TOE.goal1A5FiniteGrowthControlLevel

toe369YangMillsGoal1A45OSLimitCompilerLevel : ProofLevel
toe369YangMillsGoal1A45OSLimitCompilerLevel =
  YMGoal1TOE.goal1A45OSLimitCompilerLevel

toe369YangMillsGoal1C3OneStepAFIdentificationLevel : ProofLevel
toe369YangMillsGoal1C3OneStepAFIdentificationLevel =
  YMGoal1TOE.goal1C3OneStepAFIdentificationLevel

toe369YangMillsGoal1C3AllDepthCoefficientCompilerLevel : ProofLevel
toe369YangMillsGoal1C3AllDepthCoefficientCompilerLevel =
  YMGoal1TOE.goal1C3AllDepthCoefficientCompilerLevel

toe369YangMillsGoal1C4DensityAnchoredStressInstantiationLevel : ProofLevel
toe369YangMillsGoal1C4DensityAnchoredStressInstantiationLevel =
  YMGoal1TOE.goal1C4DensityAnchoredStressInstantiationLevel

toe369YangMillsGoal1C4SectorRecoveryCompilerLevel : ProofLevel
toe369YangMillsGoal1C4SectorRecoveryCompilerLevel =
  YMGoal1TOE.goal1C4SectorRecoveryCompilerLevel

toe369YangMillsGoal1C4LiteralSectorRecoveryLevel : ProofLevel
toe369YangMillsGoal1C4LiteralSectorRecoveryLevel =
  YMGoal1TOE.goal1C4LiteralSectorRecoveryLevel

toe369YangMillsGoal1C4CommonMetricCompilerLevel : ProofLevel
toe369YangMillsGoal1C4CommonMetricCompilerLevel =
  YMGoal1TOE.goal1C4CommonMetricCompilerLevel


toe369YangMillsGoal1ParetoZKPFrame : YMMaxCut.Goal1ParetoTOEZKPFrame
toe369YangMillsGoal1ParetoZKPFrame = YMMaxCut.canonicalGoal1ParetoTOEZKPFrame


------------------------------------------------------------------------
-- SensibLaw / legal governance TOE normalization.
-- The imported governance owner remains the theorem authority.
------------------------------------------------------------------------

toeSensibLawGovernanceSemanticBoundary :
  Authority.AuthorityNonPromotionBundle
toeSensibLawGovernanceSemanticBoundary =
  GovernanceTOE.governanceSemanticAuthorityBoundary

toeSensibLawSemanticTruthAuthorityStillClosed :
  Authority.truthAuthorityFlag toeSensibLawGovernanceSemanticBoundary ≡ false
toeSensibLawSemanticTruthAuthorityStillClosed =
  GovernanceTOE.governanceSemanticTruthAuthorityStillClosed

toeSensibLawSemanticLegalAuthorityStillClosed :
  Authority.legalAuthorityFlag toeSensibLawGovernanceSemanticBoundary ≡ false
toeSensibLawSemanticLegalAuthorityStillClosed =
  GovernanceTOE.governanceSemanticLegalAuthorityStillClosed

toeSensibLawSemanticAllAuthorityStillClosed :
  Authority.promotesAnyAuthority toeSensibLawGovernanceSemanticBoundary ≡ false
toeSensibLawSemanticAllAuthorityStillClosed =
  GovernanceTOE.governanceSemanticAllAuthorityStillClosed

toeSensibLawLegalAuthorityBoundaryReceipt :
  AuthorityBoundary.AuthorityBoundaryReceipt
toeSensibLawLegalAuthorityBoundaryReceipt =
  GovernanceTOE.governanceLegalAuthorityBoundaryReceipt

toeSensibLawLegalRuntimeContract :
  LegalRuntime.AgdaFirstLegalRuntimeContract
toeSensibLawLegalRuntimeContract =
  GovernanceTOE.governanceLegalRuntimeContract

toeSensibLawDomainTransportReceipt :
  Domain.DomainTransportReceipt
toeSensibLawDomainTransportReceipt =
  GovernanceTOE.governanceDomainTransportReceipt

toeSensibLawRepresentationEqualityDoesNotCreateLegalAuthority :
  Domain.DomainTransportReceipt.representationEqualityCreatesLegalAuthority
    toeSensibLawDomainTransportReceipt
  ≡ false
toeSensibLawRepresentationEqualityDoesNotCreateLegalAuthority =
  GovernanceTOE.governanceRepresentationEqualityDoesNotCreateLegalAuthority

toeSensibLawVendorIdentityDoesNotCreateAuthority :
  Domain.DomainTransportReceipt.vendorIdentityCreatesAuthority toeSensibLawDomainTransportReceipt
  ≡ false
toeSensibLawVendorIdentityDoesNotCreateAuthority =
  GovernanceTOE.governanceVendorIdentityDoesNotCreateAuthority

toeSensibLawTargetDomainNeedsOwnAuthorityWitness :
  Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness toeSensibLawDomainTransportReceipt
  ≡ true
toeSensibLawTargetDomainNeedsOwnAuthorityWitness =
  GovernanceTOE.governanceTargetDomainNeedsOwnAuthorityWitness

toeSensibLawGovernanceZKPFrame :
  GovernanceTOE.SensibLawGovernanceTOEZKPFrame
toeSensibLawGovernanceZKPFrame =
  GovernanceTOE.canonicalSensibLawGovernanceTOEZKPFrame
