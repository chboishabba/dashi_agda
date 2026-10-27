{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact where

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F
--
-- O. Objective.
-- Connect the current Yang-Mills source frontier to the DASHI TOE graph.
-- Reuse existing theorem owners.
-- Do not create a second RG, stress, Casimir, continuum, or Clay ontology.
--
-- R. Reuse.
-- R219 owns beta-driven CMP119 density and coupling coordinates.
-- R225 owns the preferred regular-E localization frontier.
-- CompactSimpleClassificationAdjointCasimirExact owns exact C_A positivity.
-- Round106 owns the canonical metric-stress representation compiler.
-- YMClayOSLiteralStressRouteParetoExact owns stress/OPE route separation.
-- R474 owns the authoritative least-privilege Goal-1 Clay frontier.
-- R521 owns the concrete-semantics residual with zero opaque endpoint leaves.
-- R546 owns the authoritative fourteen-family irreducible source frontier.
-- R558 owns the seven-family critical mass-gap/nontriviality path.
-- YMClayPromotionBoundary owns the terminal fail-closed Clay boundary.
--
-- C. Concrete result.
-- This file exposes exact theorem levels, current family counts, current
-- semantic firewalls, and exact non-promotion proofs.
--
-- S. Scope and invariants.
-- A compiler fact is not a source theorem.
-- A source citation is not a same-object proof.
-- A finite RG identity is not a continuum Yang-Mills theorem.
-- C_A positivity is not the Wilson/ghost/Haar colour contraction.
-- A stress representation compiler is not the literal stress/OPE theorem.
-- A family count is a scheduling quotient, not a theorem count.
-- A TOE import edge cannot promote a Clay solution.
--
-- L. Lane.
-- This file is the Yang-Mills TOE integration lane.
-- It does not edit ESD or digital_esd modules.
-- It does not copy code from meta-introspector repositories.
--
-- P. Postcondition.
-- TOE consumers reach canonical RG, regular-E, Casimir, stress, irreducible
-- Goal-1, source-family, critical-path, concrete-semantics, and Clay-boundary owners
-- through one normalized surface.
--
-- G. Governance.
-- One claim uses one canonical owner.
-- Original mathematical and repository attribution stays with each owner.
-- Fail-closed promotion proofs remain explicit.
--
-- F. Verification.
-- Source read-back must find every import and theorem below.
-- Kernel certification requires an exact-head Agda or CI receipt.
--
-- Preconditions.
-- The canonical source owners already exist in the repository.
-- Each compiler keeps its original proof level.
-- Each literal source seam keeps its original proof level.
-- The TOE graph imports this owner instead of copying source proofs.
--
-- Invariants.
-- One source fact has one canonical theorem owner.
-- The selected RG density keeps one scale identity across the action and stress lanes.
-- Finite RG facts do not create a continuum theorem.
-- Casimir positivity does not create a missing colour-contraction theorem.
-- Stress compilation does not create a literal stress/OPE source theorem.
-- ESD and digital_esd surfaces remain unchanged.
--
-- Postconditions.
-- The TOE root reaches the canonical Goal-1, density, action, regular-E, Casimir, and stress owners.
-- Unified.Physics reaches the same normalized aliases.
-- Unifier reaches the same normalized aliases.
-- The continuum, OS/Wightman, mass-gap, and Clay promotion gates remain false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.Balaban1989BetaHistoryToCanonicalCompleteDensityExact as CanonicalDensity
import DASHI.Physics.YangMills.BalabanPreferredRegularEFrontierRound225Exact as R225
import DASHI.Physics.YangMills.BalabanPublishedFlowToRegularEProjectionRound241Exact as R241
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as R244
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanCMP119RawActiveRegularEDecoderRound248Exact as R248
import DASHI.Physics.YangMills.BalabanPublishedUVStabilityNonlinearRGCoreExact as PublishedRG
import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact as Casimir
import DASHI.Physics.YangMills.BalabanCompactSimpleUniversalBetaFloorExact as BetaFloor
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as Stress106
import DASHI.Physics.YangMills.BalabanCMP116FirstVariationStressPairingRound105Exact as Stress105
import DASHI.Physics.YangMills.BalabanStressShellEnergyToHilbertRound112Exact as Stress112
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as GeneratedDensity132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionStressScaleRound135Exact as StressScale135
import DASHI.Physics.YangMills.BalabanCombinedRGUnifiedActionRound141Exact as CombinedAction141
import DASHI.Physics.YangMills.YMClayOSLiteralStressRouteParetoExact as StressPareto
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound84SixAnalyticLemmaExact as Stress84
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound85SixAnalyticLemmaAttackExact as Stress85
import DASHI.Physics.YangMills.YangMillsClayGoal1CurrentFrontierRound474Exact as R474
import DASHI.Physics.YangMills.YangMillsClayConcreteSemanticsResidualRound521Exact as R521
import DASHI.Physics.YangMills.YangMillsClayIrreducibleSourceFamiliesRound546Exact as R546
import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound558Exact as R558
import DASHI.Physics.Closure.YMClayPromotionBoundary as Promotion
import DASHI.Physics.Closure.YMBTToFourDimensionalContinuumRouteBoundary as ContinuumBoundary


------------------------------------------------------------------------
-- Exact theorem-owner re-exports.
--
-- Re-export canonical theorem owners.
-- Do not duplicate their proofs.
------------------------------------------------------------------------

open BetaDensity public using
  ( sourceCouplingIsBetaHistoryCoupling
  ; sourceSmallnessIsDerivedFromBetaHistory
  )

open CanonicalDensity public using
  ( betaHistoryGivesRepositoryCouplingCap
  ; canonicalStateRunningCouplingIsBetaHistory
  ; betaHistoryAndSourceTheoremGiveLiteralInvariantRegion
  )

open GeneratedDensity132 public using
  ( selectedDensityRepresentsExactBC1Potential
  ; selectedDensityRepresentsBC2InitialPotential
  )

open StressScale135 public using
  ( stressSelectedDensityIndexIsUnifiedActionIndex
  )

open Stress105 public using
  ( sourceDerivativeBelowExistingMarkedShell
  )

open Stress112 public using
  ( stressCoefficientEnergyUniformBound
  ; stressPairingSquaredCauchyFromShellEnergy
  )

open R244 public using
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
-- Balaban RG density and regular-E localization.
------------------------------------------------------------------------

toeBetaDrivenResidualFamilyCompilerLevel : ProofLevel
toeBetaDrivenResidualFamilyCompilerLevel =
  R219.betaDrivenCMP119ResidualFamilyCompilerLevel

toeBetaDensityAndCouplingSameObjectLevel : ProofLevel
toeBetaDensityAndCouplingSameObjectLevel =
  R219.betaDensityAndCouplingSameObjectCompilerLevel

toeLiteralBetaDrivenResidualFamilyLevel : ProofLevel
toeLiteralBetaDrivenResidualFamilyLevel =
  R219.literalBetaDrivenCMP119ResidualFamilyLevel

toeLiteralBetaDrivenDifferentiatedCoordinateLevel : ProofLevel
toeLiteralBetaDrivenDifferentiatedCoordinateLevel =
  R219.literalBetaDrivenCMP119DifferentiatedCoordinateLevel

-- Exact same-object RG density/coupling owners.
-- These are not new RG facts.
-- They expose the canonical repository identity between the finite beta history,
-- the CMP122 effective-density flow, and the canonical complete-density state.
toeBetaDrivenSourceFlowLevel : ProofLevel
toeBetaDrivenSourceFlowLevel =
  BetaDensity.balabanBetaDrivenSourceFlowLevel

toeBetaHistoryIsLiteralCMP122CouplingLevel : ProofLevel
toeBetaHistoryIsLiteralCMP122CouplingLevel =
  BetaDensity.balabanBetaHistoryIsLiteralCMP122CouplingLevel

toeBetaHistorySameStateCouplingLevel : ProofLevel
toeBetaHistorySameStateCouplingLevel =
  CanonicalDensity.balabanBetaHistorySameStateCouplingLevel

toeBetaHistoryToCanonicalCompleteDensityLevel : ProofLevel
toeBetaHistoryToCanonicalCompleteDensityLevel =
  CanonicalDensity.balabanBetaHistoryToCanonicalCompleteDensityLevel

-- Round132 is the canonical same-action weld.
-- It maps the selected beta-driven density to the exact BC1/BC2 effective potential.
-- The compiler is checked.
-- The literal source realization remains conditional.
toeUnifiedGeneratedActionDensityCompilerLevel : ProofLevel
toeUnifiedGeneratedActionDensityCompilerLevel =
  GeneratedDensity132.unifiedGeneratedActionDensityCompilerLevel

toeLiteralUnifiedGeneratedActionDensityLevel : ProofLevel
toeLiteralUnifiedGeneratedActionDensityLevel =
  GeneratedDensity132.literalUnifiedGeneratedActionDensityLevel

-- Round141 reuses the existing CombinedRG trajectory.
-- It connects the complete density to the same effective-action realization.
-- It does not create a second RG state.
toeCompleteDensityEffectiveActionRealizationCompilerLevel : ProofLevel
toeCompleteDensityEffectiveActionRealizationCompilerLevel =
  CombinedAction141.completeDensityEffectiveActionRealizationCompilerLevel

toeLiteralCompleteDensityEffectiveActionRealizationLevel : ProofLevel
toeLiteralCompleteDensityEffectiveActionRealizationLevel =
  CombinedAction141.literalCompleteDensityEffectiveActionRealizationLevel

toeRegularESourceProjectionLevel : ProofLevel
toeRegularESourceProjectionLevel =
  R225.regularESourceProjectionLevel

toeRegularEPointwiseLocalizationLevel : ProofLevel
toeRegularEPointwiseLocalizationLevel =
  R225.regularEPointwiseLocalizationLevel

toeRegularEContinuationCompilerLevel : ProofLevel
toeRegularEContinuationCompilerLevel =
  R225.regularEContinuationCompilerLevel

toeRegularEBC1CompilerLevel : ProofLevel
toeRegularEBC1CompilerLevel =
  R225.regularEBC1CompilerLevel

toeRegularEPhysicalSourceClosure : Bool
toeRegularEPhysicalSourceClosure =
  R225.round225PhysicalSourceClosure

toeRegularEPhysicalSourceClosureIsFalse :
  toeRegularEPhysicalSourceClosure ≡ false
toeRegularEPhysicalSourceClosureIsFalse =
  R225.round225PhysicalSourceClosureIsFalse

------------------------------------------------------------------------
-- Source-native regular-E normalization.
--
-- These aliases keep the older preferred frontier for compatibility.
-- They also expose the later source-native path that starts from the literal
-- published density, selected regular-E coordinate, and active localization.
------------------------------------------------------------------------

toePublishedFlowToRegularEProjectionCompilerLevel : ProofLevel
toePublishedFlowToRegularEProjectionCompilerLevel =
  R241.publishedFlowToRegularEProjectionCompilerLevel

toeCMP119RegularELocalizationSourceLevel : ProofLevel
toeCMP119RegularELocalizationSourceLevel =
  R244.cmp119RegularELocalizationSourceLevel

toeLiteralCMP119RegularELocalizationCarrierLevel : ProofLevel
toeLiteralCMP119RegularELocalizationCarrierLevel =
  R244.literalCMP119RegularELocalizationCarrierLevel

toeRegularESection2PredicateCompilerLevel : ProofLevel
toeRegularESection2PredicateCompilerLevel =
  R246.regularESection2PredicateCompilerLevel

toeConcreteELocalizationSourceWitnessLevel : ProofLevel
toeConcreteELocalizationSourceWitnessLevel =
  R248.literalCMP122Theorem1OnConcreteELocalizationPredicateLevel

------------------------------------------------------------------------
-- Published nonlinear RG and continuum non-promotion.
------------------------------------------------------------------------

toePublishedFourDimensionalNonlinearRGCoreLevel : ProofLevel
toePublishedFourDimensionalNonlinearRGCoreLevel =
  PublishedRG.publishedFourDimensionalNonlinearRGCoreLevel

toePublishedRGPhysicalSameObjectLevel : ProofLevel
toePublishedRGPhysicalSameObjectLevel =
  PublishedRG.literalPhysicalStateToPublishedRGCarrierLevel

toeFlat4DContinuumTransferProvedHere : Bool
toeFlat4DContinuumTransferProvedHere =
  ContinuumBoundary.flat4DContinuumTransferProvedHere

toeFlat4DContinuumTransferProvedHereIsFalse :
  toeFlat4DContinuumTransferProvedHere ≡ false
toeFlat4DContinuumTransferProvedHereIsFalse =
  refl

toeContinuumMassGapPromoted : Bool
toeContinuumMassGapPromoted =
  ContinuumBoundary.continuumMassGapPromoted

toeContinuumMassGapPromotedIsFalse :
  toeContinuumMassGapPromoted ≡ false
toeContinuumMassGapPromotedIsFalse =
  refl

-- Exact non-promotion theorem.
-- A published finite RG stability owner does not construct the missing
-- four-dimensional continuum-transfer theorem.
toePublishedRGDoesNotPromoteContinuum :
  toeFlat4DContinuumTransferProvedHere ≡ false
toePublishedRGDoesNotPromoteContinuum =
  toeFlat4DContinuumTransferProvedHereIsFalse

-- The same boundary applies after the density/action normalization.
-- Round132 and Round141 are finite same-object compilers.
-- They do not construct the missing continuum transfer.
toeGeneratedActionDensityDoesNotPromoteContinuum :
  toeFlat4DContinuumTransferProvedHere ≡ false
toeGeneratedActionDensityDoesNotPromoteContinuum =
  toeFlat4DContinuumTransferProvedHereIsFalse

toeCombinedRGUnifiedActionDoesNotPromoteContinuum :
  toeFlat4DContinuumTransferProvedHere ≡ false
toeCombinedRGUnifiedActionDoesNotPromoteContinuum =
  toeFlat4DContinuumTransferProvedHereIsFalse

toeDepthLimitNoSpectralPollutionProvedHere : Bool
toeDepthLimitNoSpectralPollutionProvedHere =
  ContinuumBoundary.depthLimitNoSpectralPollutionProvedHere

toeDepthLimitNoSpectralPollutionProvedHereIsFalse :
  toeDepthLimitNoSpectralPollutionProvedHere ≡ false
toeDepthLimitNoSpectralPollutionProvedHereIsFalse =
  ContinuumBoundary.depthLimitNoSpectralPollutionProvedHereIsFalse

toeOSWightmanContinuumConstructionProvedHere : Bool
toeOSWightmanContinuumConstructionProvedHere =
  ContinuumBoundary.osWightmanContinuumConstructionProvedHere

toeOSWightmanContinuumConstructionProvedHereIsFalse :
  toeOSWightmanContinuumConstructionProvedHere ≡ false
toeOSWightmanContinuumConstructionProvedHereIsFalse =
  ContinuumBoundary.osWightmanContinuumConstructionProvedHereIsFalse

toeTerminalPromotion : Bool
toeTerminalPromotion =
  ContinuumBoundary.terminalPromotion

toeTerminalPromotionIsFalse :
  toeTerminalPromotion ≡ false
toeTerminalPromotionIsFalse =
  ContinuumBoundary.terminalPromotionIsFalse

------------------------------------------------------------------------
-- Compact-simple Casimir and stress.
------------------------------------------------------------------------

toeAdjointCasimirStrictPositivityLevel : ProofLevel
toeAdjointCasimirStrictPositivityLevel =
  Casimir.classificationAdjointCasimirStrictPositivityLevel


toeCompactSimpleUniversalBetaFloorLevel : ProofLevel
toeCompactSimpleUniversalBetaFloorLevel =
  BetaFloor.compactSimpleUniversalBetaFloorLevel

toeLiteralUniformRegularRemainderBelowUniversalFloorLevel : ProofLevel
toeLiteralUniformRegularRemainderBelowUniversalFloorLevel =
  BetaFloor.literalUniformRegularRemainderBelowUniversalFloorLevel

toeWilsonGhostHaarToClassifiedCasimirLevel : ProofLevel
toeWilsonGhostHaarToClassifiedCasimirLevel =
  Casimir.literalWilsonGhostHaarToClassifiedCasimirLevel

toeStrictCasimirCarrierCompilerLevel : ProofLevel
toeStrictCasimirCarrierCompilerLevel =
  Casimir.classificationToStrictCasimirCarrierLevel

toeMetricStressRepresentationCompilerLevel : ProofLevel
toeMetricStressRepresentationCompilerLevel =
  Stress106.canonicalMetricStressRepresentationCompilerLevel

toeLiteralMetricStressRepresentationLevel : ProofLevel
toeLiteralMetricStressRepresentationLevel =
  Stress106.literalCMP116MetricStressRepresentationLevel


toeStressFirstVariationMarkedShellBoundLevel : ProofLevel
toeStressFirstVariationMarkedShellBoundLevel =
  Stress105.cmp116StressReusesFirstGradientMarkedShellLevel

toeLiteralStressMetricSourceCoordinateWeldLevel : ProofLevel
toeLiteralStressMetricSourceCoordinateWeldLevel =
  Stress105.literalCMP116MetricSourceCoordinateWeldLevel

toeLiteralFirstVariationStressPairingLevel : ProofLevel
toeLiteralFirstVariationStressPairingLevel =
  Stress105.literalCMP116FirstVariationStressPairingLevel

toeStressShellEnergyToHilbertCompilerLevel : ProofLevel
toeStressShellEnergyToHilbertCompilerLevel =
  Stress112.stressShellEnergyToHilbertCompilerLevel

toeLiteralStressActivityEntropyInstantiationLevel : ProofLevel
toeLiteralStressActivityEntropyInstantiationLevel =
  Stress112.literalStressCMP116ActivityEntropyInstantiationLevel

toeLiteralStressCoefficientEnergyShellPrefixLevel : ProofLevel
toeLiteralStressCoefficientEnergyShellPrefixLevel =
  Stress112.literalStressCoefficientEnergyIsShellPrefixLevel

toeUnifiedGeneratedActionStressScaleCompilerLevel : ProofLevel
toeUnifiedGeneratedActionStressScaleCompilerLevel =
  StressScale135.unifiedGeneratedActionStressScaleCompilerLevel

toeLiteralUnifiedGeneratedActionStressScaleLevel : ProofLevel
toeLiteralUnifiedGeneratedActionStressScaleLevel =
  StressScale135.literalUnifiedGeneratedActionStressScaleLevel

toeStressRouteClayPromotion : Bool
toeStressRouteClayPromotion =
  StressPareto.clayPromotion

toeStressRouteClayPromotionIsFalse :
  toeStressRouteClayPromotion ≡ false
toeStressRouteClayPromotionIsFalse =
  StressPareto.clayPromotionIsFalse

toeStressLevel2SameFamilyRecoveryLevel : ProofLevel
toeStressLevel2SameFamilyRecoveryLevel =
  StressPareto.level2SameFamilyRecoveryLevel

toeStressLevel2ShortDistanceOPELevel : ProofLevel
toeStressLevel2ShortDistanceOPELevel =
  StressPareto.level2ShortDistanceOPEStressAFLevel

------------------------------------------------------------------------
-- Current Casimir/stress hard-analysis cutset.
--
-- Round84 keeps the conservative six-family count.
-- Round85 exposes the exact remaining physical leaves.
-- Downstream compiler facts stay distinct from those leaves.
------------------------------------------------------------------------

toeHardAnalyticLemmaUpperCount : Nat
toeHardAnalyticLemmaUpperCount =
  Stress84.round84HardAnalyticLemmaUpperCount

toeHardAnalyticLemmaUpperCountIsSix :
  toeHardAnalyticLemmaUpperCount ≡ 6
toeHardAnalyticLemmaUpperCountIsSix = refl

toeLiteralWilsonFPHaarFourJointOrbitHalfEnclosuresLevel : ProofLevel
toeLiteralWilsonFPHaarFourJointOrbitHalfEnclosuresLevel =
  Stress85.literalWilsonFPHaarFourJointOrbitHalfEnclosuresLevel

toePhysicalMarkedCoordinateRadiusProjectionAndCompositeHilbertModulusLevel : ProofLevel
toePhysicalMarkedCoordinateRadiusProjectionAndCompositeHilbertModulusLevel =
  Stress85.physicalMarkedCoordinateRadiusProjectionAndCompositeHilbertModulusLevel

toePhysicalPerShellHeatHessianDebtLevel : ProofLevel
toePhysicalPerShellHeatHessianDebtLevel =
  Stress85.physicalPerShellHeatHessianDebtLevel

toePhysicalSameFamilyOPEProductAndOneStepAFIdentificationLevel : ProofLevel
toePhysicalSameFamilyOPEProductAndOneStepAFIdentificationLevel =
  Stress85.physicalSameFamilyOPEProductAndOneStepAFIdentificationLevel

toePhysicalStressWardCommonCoreAndEssentialSelfAdjointnessLevel : ProofLevel
toePhysicalStressWardCommonCoreAndEssentialSelfAdjointnessLevel =
  Stress85.physicalStressWardCommonCoreAndEssentialSelfAdjointnessLevel

toeCompactSimpleUniversalCasimirFloorLevel : ProofLevel
toeCompactSimpleUniversalCasimirFloorLevel =
  Stress85.compactSimpleUniversalCasimirFloorLevel

toeStressChargeLocalCoreCutoffRemovalLevel : ProofLevel
toeStressChargeLocalCoreCutoffRemovalLevel =
  Stress85.stressChargeLocalCoreCutoffRemovalLevel

------------------------------------------------------------------------
-- Current Goal-1 Clay frontier.
--
-- R474 is the preferred least-privilege Goal-1 route.
-- R546/R558 remain the broader normalized source-family and critical-path views.
------------------------------------------------------------------------

toeGoal1FiniteSymmetryAndRPApplicationLevel : ProofLevel
toeGoal1FiniteSymmetryAndRPApplicationLevel =
  R474.aFiniteSymmetryAndRPApplicationLevel

toeGoal1A1CurrentStepBetaSourceLevel : ProofLevel
toeGoal1A1CurrentStepBetaSourceLevel =
  R474.a1CurrentStepBetaSourceLevel

toeGoal1A2HistoryBetaShellSameObjectLevel : ProofLevel
toeGoal1A2HistoryBetaShellSameObjectLevel =
  R474.a2HistoryBetaShellSameObjectLevel

toeGoal1A3SameFamilyContinuumAndOSLevel : ProofLevel
toeGoal1A3SameFamilyContinuumAndOSLevel =
  R474.a3SameFamilyContinuumAndOSLevel

toeGoal1A45MomentToOS05Level : ProofLevel
toeGoal1A45MomentToOS05Level =
  R474.a45MomentToOS05Level

toeGoal1BLiteralPublishedSelectedLocalizationLevel : ProofLevel
toeGoal1BLiteralPublishedSelectedLocalizationLevel =
  R474.bLiteralPublishedSelectedLocalizationLevel

toeGoal1BPhysicalRateSemanticsLevel : ProofLevel
toeGoal1BPhysicalRateSemanticsLevel =
  R474.bPhysicalRateSemanticsLevel

toeGoal1BFiniteToPositiveTransferGapCompilerLevel : ProofLevel
toeGoal1BFiniteToPositiveTransferGapCompilerLevel =
  R474.bFiniteToPositiveTransferGapCompilerLevel

toeGoal1BLiteralClayT2SemanticsLevel : ProofLevel
toeGoal1BLiteralClayT2SemanticsLevel =
  R474.bLiteralClayT2SemanticsLevel

toeGoal1CStressFiniteSameFamilySourceLevel : ProofLevel
toeGoal1CStressFiniteSameFamilySourceLevel =
  R474.cStressFiniteSameFamilySourceLevel

toeGoal1CStressLiteralDensityDerivativeLevel : ProofLevel
toeGoal1CStressLiteralDensityDerivativeLevel =
  R474.cStressLiteralDensityDerivativeLevel

toeGoal1CStressSameFamilyOSRecoveryLevel : ProofLevel
toeGoal1CStressSameFamilyOSRecoveryLevel =
  R474.cStressSameFamilyOSRecoveryLevel

toeGoal1CPhysicalOPERemainderIsMarkedTailLevel : ProofLevel
toeGoal1CPhysicalOPERemainderIsMarkedTailLevel =
  R474.cPhysicalOPERemainderIsMarkedTailLevel

toeGoal1COneStepAFRGIdentificationLevel : ProofLevel
toeGoal1COneStepAFRGIdentificationLevel =
  R474.cOneStepAFRGIdentificationLevel

toeGoal1CExactSameFamilySourceCutLevel : ProofLevel
toeGoal1CExactSameFamilySourceCutLevel =
  R474.cExactSameFamilySourceCutLevel

toeGoal1G1ArbitraryCompactSimpleSourceMapLevel : ProofLevel
toeGoal1G1ArbitraryCompactSimpleSourceMapLevel =
  R474.g1ArbitraryCompactSimpleSelectedBackgroundSourceMapLevel

toeGoal1G2SameSystemNontrivialitySemanticsLevel : ProofLevel
toeGoal1G2SameSystemNontrivialitySemanticsLevel =
  R474.g2SameSystemClayNontrivialitySemanticsLevel

toeGoal1TerminalCompilerLevel : ProofLevel
toeGoal1TerminalCompilerLevel =
  R474.round474TerminalCompilerLevel

toeGoal1CurrentFrontierCompilerLevel : ProofLevel
toeGoal1CurrentFrontierCompilerLevel =
  R474.round474CurrentFrontierCompilerLevel

toeGoal1ExplicitPeterWeylRPMandatory : Bool
toeGoal1ExplicitPeterWeylRPMandatory =
  R474.explicitPeterWeylRPMandatory

toeGoal1ProjectiveProkhorovMandatory : Bool
toeGoal1ProjectiveProkhorovMandatory =
  R474.projectiveProkhorovMandatory

toeGoal1IndependentKPDatumSelectionMandatory : Bool
toeGoal1IndependentKPDatumSelectionMandatory =
  R474.independentKPDatumSelectionMandatory

toeGoal1PostHocCMP116MagnitudeEqualityMandatory : Bool
toeGoal1PostHocCMP116MagnitudeEqualityMandatory =
  R474.postHocCMP116MagnitudeEqualityMandatory

toeGoal1IndependentFourthCumulantMandatory : Bool
toeGoal1IndependentFourthCumulantMandatory =
  R474.independentFourthCumulantMandatory

------------------------------------------------------------------------
-- Current normalized source frontier.
------------------------------------------------------------------------

toeIrreducibleSourceFamilyCount : Nat
toeIrreducibleSourceFamilyCount =
  R546.preferredSourceFamilyCount

toeIrreducibleSourceFamilyCountIsFourteen :
  toeIrreducibleSourceFamilyCount ≡ 14
toeIrreducibleSourceFamilyCountIsFourteen = refl

toeCriticalFamilyCount : Nat
toeCriticalFamilyCount =
  R558.criticalFamilyCount

toeCriticalFamilyCountIsSeven :
  toeCriticalFamilyCount ≡ 7
toeCriticalFamilyCountIsSeven = refl

toeOpaqueEndpointPredicatesRemaining : Bool
toeOpaqueEndpointPredicatesRemaining =
  R546.opaqueEndpointPredicatesRemaining

toeOpaqueEndpointPredicatesRemainingIsFalse :
  toeOpaqueEndpointPredicatesRemaining ≡ false
toeOpaqueEndpointPredicatesRemainingIsFalse = refl

toeConstructorChoiceEqualitiesRemaining : Bool
toeConstructorChoiceEqualitiesRemaining =
  R546.constructorChoiceEqualitiesRemaining

toeConstructorChoiceEqualitiesRemainingIsFalse :
  toeConstructorChoiceEqualitiesRemaining ≡ false
toeConstructorChoiceEqualitiesRemainingIsFalse = refl

toeAllRemainingFamiliesAlreadyProved : Bool
toeAllRemainingFamiliesAlreadyProved =
  R546.allRemainingFamiliesAreAlreadyProved

toeAllRemainingFamiliesAlreadyProvedIsFalse :
  toeAllRemainingFamiliesAlreadyProved ≡ false
toeAllRemainingFamiliesAlreadyProvedIsFalse = refl

------------------------------------------------------------------------
-- Concrete semantics residual.
------------------------------------------------------------------------

toeConcreteSemanticResidualCount : Nat
toeConcreteSemanticResidualCount =
  R521.residualLeafCount

toeConcreteSemanticResidualCountIsThirtyThree :
  toeConcreteSemanticResidualCount ≡ 33
toeConcreteSemanticResidualCountIsThirtyThree = refl

toeEndpointSemanticResidualCount : Nat
toeEndpointSemanticResidualCount =
  R521.endpointSemanticLeafCount

toeEndpointSemanticResidualCountIsZero :
  toeEndpointSemanticResidualCount ≡ 0
toeEndpointSemanticResidualCountIsZero = refl

------------------------------------------------------------------------
-- Critical-path exclusions.
------------------------------------------------------------------------

toeSeparateContinuumWilsonFamilyRequired : Bool
toeSeparateContinuumWilsonFamilyRequired =
  R558.separateContinuumWilsonConvergenceFamilyRequired

toeSeparateContinuumWilsonFamilyRequiredIsFalse :
  toeSeparateContinuumWilsonFamilyRequired ≡ false
toeSeparateContinuumWilsonFamilyRequiredIsFalse = refl

toeFiniteHamiltonianMoscoRouteRequired : Bool
toeFiniteHamiltonianMoscoRouteRequired =
  R558.finiteHamiltonianMoscoRouteRequired

toeFiniteHamiltonianMoscoRouteRequiredIsFalse :
  toeFiniteHamiltonianMoscoRouteRequired ≡ false
toeFiniteHamiltonianMoscoRouteRequiredIsFalse = refl

toeFullCLayerRetainedForConservativeClayExistence : Bool
toeFullCLayerRetainedForConservativeClayExistence =
  R558.fullCLayerRetainedForConservativeClayExistence

------------------------------------------------------------------------
-- Exact non-promotion boundary.
------------------------------------------------------------------------

toeAllClayProvidersDerivedInRepo : Bool
toeAllClayProvidersDerivedInRepo =
  Promotion.allProvidersDerivedInRepo

toeAllClayProvidersDerivedInRepoIsFalse :
  toeAllClayProvidersDerivedInRepo ≡ false
toeAllClayProvidersDerivedInRepoIsFalse =
  Promotion.ClayPromotionBoundary.allProvidersDerivedInRepoIsFalse
    Promotion.clayPromotionBoundary

toeClayStatementBoundaryDischarged : Bool
toeClayStatementBoundaryDischarged =
  Promotion.clayStatementBoundaryDischarged

toeClayStatementBoundaryDischargedIsFalse :
  toeClayStatementBoundaryDischarged ≡ false
toeClayStatementBoundaryDischargedIsFalse =
  Promotion.ClayPromotionBoundary.clayStatementBoundaryDischargedIsFalse
    Promotion.clayPromotionBoundary

toeClayYangMillsPromoted : Bool
toeClayYangMillsPromoted =
  Promotion.clayYangMillsPromoted

toeClayYangMillsPromotedIsFalse :
  toeClayYangMillsPromoted ≡ false
toeClayYangMillsPromotedIsFalse =
  Promotion.ClayPromotionBoundary.noClayPromotion
    Promotion.clayPromotionBoundary

round559TOEConvergenceCompilerLevel : ProofLevel
round559TOEConvergenceCompilerLevel = machineChecked
