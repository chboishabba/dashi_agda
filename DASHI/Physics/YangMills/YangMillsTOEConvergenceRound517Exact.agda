{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsTOEConvergenceRound517Exact where

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F
--
-- O. Objective.
-- Reuse the existing Yang-Mills source owners in the DASHI TOE graph.
-- Do not create a second RG, stress, Casimir, continuum, or Clay ontology.
--
-- R. Reuse.
-- R219 owns beta-driven CMP119 density and coupling coordinates.
-- R225 owns the preferred regular-E frontier.
-- CompactSimpleClassificationAdjointCasimirExact owns exact C_A positivity.
-- Round106 owns the canonical metric-stress representation compiler.
-- YMClayOSLiteralStressRouteParetoExact owns stress/OPE route separation.
-- R515 owns the current 15/18/21 residual cut.
-- YMClayPromotionBoundary owns the terminal fail-closed Clay boundary.
--
-- C. Concrete result.
-- This file imports those owners and exposes only their exact theorem levels,
-- exact same-object equalities, residual counts, and non-promotion proofs.
--
-- S. Scope and invariants.
-- A compiler fact is not a source theorem.
-- A source citation is not a same-object proof.
-- A finite RG identity is not a continuum Yang-Mills theorem.
-- A stress representation compiler is not the literal stress/OPE endpoint.
-- C_A positivity is not the Wilson/ghost/Haar colour contraction.
-- A TOE import edge cannot promote a Clay solution.
--
-- L. Lane.
-- This file is the Yang-Mills TOE integration lane.
-- It does not edit any ESD or digital_esd module.
-- It does not copy code from meta-introspector repositories.
--
-- P. Postcondition.
-- TOE consumers reach the canonical YM RG, regular-E, Casimir, stress,
-- residual, and Clay-boundary owners through one normalized import surface.
--
-- G. Governance.
-- The change uses one canonical owner per claim.
-- It preserves source attribution.
-- It keeps fail-closed promotion flags.
-- It uses direct theorem reuse instead of duplicate abstractions.
--
-- F. Verification.
-- Exact source read-back must find every imported owner and theorem below.
-- Kernel certification requires an exact-head Agda or CI receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanPreferredRegularEFrontierRound225Exact as R225
import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact as Casimir
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as Stress106
import DASHI.Physics.YangMills.YMClayOSLiteralStressRouteParetoExact as StressPareto
import DASHI.Physics.YangMills.YangMillsClayPostQuantitativeResidualRound515Exact as R515
import DASHI.Physics.Closure.YMClayPromotionBoundary as Promotion

------------------------------------------------------------------------
-- RG density and coupling.
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

------------------------------------------------------------------------
-- Preferred regular-E source frontier.
------------------------------------------------------------------------

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

toeRegularEClayPromotion : Bool
toeRegularEClayPromotion =
  R225.round225ClayPromotion

toeRegularEClayPromotionIsFalse :
  toeRegularEClayPromotion ≡ false
toeRegularEClayPromotionIsFalse =
  R225.round225ClayPromotionIsFalse

------------------------------------------------------------------------
-- Compact-simple Casimir.
------------------------------------------------------------------------

toeAdjointCasimirFormulaLevel : ProofLevel
toeAdjointCasimirFormulaLevel =
  Casimir.classificationAdjointCasimirFormulaLevel

toeAdjointCasimirStrictPositivityLevel : ProofLevel
toeAdjointCasimirStrictPositivityLevel =
  Casimir.classificationAdjointCasimirStrictPositivityLevel

toeClassificationToStrictCasimirCarrierLevel : ProofLevel
toeClassificationToStrictCasimirCarrierLevel =
  Casimir.classificationToStrictCasimirCarrierLevel

toeWilsonGhostHaarToClassifiedCasimirLevel : ProofLevel
toeWilsonGhostHaarToClassifiedCasimirLevel =
  Casimir.literalWilsonGhostHaarToClassifiedCasimirLevel

------------------------------------------------------------------------
-- Stress and OPE.
------------------------------------------------------------------------

toeMetricStressRepresentationCompilerLevel : ProofLevel
toeMetricStressRepresentationCompilerLevel =
  Stress106.canonicalMetricStressRepresentationCompilerLevel

toeLiteralMetricStressRepresentationLevel : ProofLevel
toeLiteralMetricStressRepresentationLevel =
  Stress106.literalCMP116MetricStressRepresentationLevel

toeOSReconstructionMachineryMissing : Bool
toeOSReconstructionMachineryMissing =
  StressPareto.osReconstructionMachineryMissing

toeOSReconstructionMachineryMissingIsFalse :
  toeOSReconstructionMachineryMissing ≡ false
toeOSReconstructionMachineryMissingIsFalse =
  StressPareto.osReconstructionMachineryMissingIsFalse

toeStressRouteClayPromotion : Bool
toeStressRouteClayPromotion =
  StressPareto.clayPromotion

toeStressRouteClayPromotionIsFalse :
  toeStressRouteClayPromotion ≡ false
toeStressRouteClayPromotionIsFalse =
  StressPareto.clayPromotionIsFalse

------------------------------------------------------------------------
-- Current exact residual cut.
------------------------------------------------------------------------

toeSourceAnalysisResidualCount : Nat
toeSourceAnalysisResidualCount =
  R515.sourceAnalysisLeafCount

toeSourceLiteralAttachmentResidualCount : Nat
toeSourceLiteralAttachmentResidualCount =
  R515.sourceLiteralAttachmentLeafCount

toeEndpointSemanticResidualCount : Nat
toeEndpointSemanticResidualCount =
  R515.endpointSemanticLeafCount

toeTotalResidualCount : Nat
toeTotalResidualCount =
  R515.residualLeafCount

toeSourceAnalysisResidualCountIsFifteen :
  toeSourceAnalysisResidualCount ≡ 15
toeSourceAnalysisResidualCountIsFifteen = refl

toeSourceLiteralAttachmentResidualCountIsEighteen :
  toeSourceLiteralAttachmentResidualCount ≡ 18
toeSourceLiteralAttachmentResidualCountIsEighteen = refl

toeEndpointSemanticResidualCountIsTwentyOne :
  toeEndpointSemanticResidualCount ≡ 21
toeEndpointSemanticResidualCountIsTwentyOne = refl

toeTotalResidualCountIsFiftyFour :
  toeTotalResidualCount ≡ 54
toeTotalResidualCountIsFiftyFour = refl

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

round517TOEConvergenceCompilerLevel : ProofLevel
round517TOEConvergenceCompilerLevel = machineChecked
