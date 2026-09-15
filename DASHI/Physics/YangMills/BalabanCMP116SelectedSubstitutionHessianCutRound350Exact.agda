{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedSubstitutionHessianCutRound350Exact where

------------------------------------------------------------------------
-- ROUND350 / SPLIT R347 BOUNDARY DEBT AT THE GENERIC COMPILER ABI
--
-- `BalabanDecoupledActivityHessian.markedSubstitutionStabilityLiftsToCoefficient`
-- shows that the generic Cauchy/coefficient part of R347 consumes only two
-- source-specific quantitative ingredients once nonnegativity and common-domain
-- admissibility are available:
--
--   S_sub:
--     the selected substituted-background displacement on each boundary
--     assignment is controlled by the selected marked input;
--
--   S_Hess:
--     the selected local-activity Hessian is Lipschitz with respect to that
--     substituted-background displacement on the SAME common analytic domain.
--
-- The R103/R104 common-radius lane already owns the *existence/admissibility*
-- plumbing for the background/source/local-activity/substituted-background
-- coordinates after the finite normalized source demands are supplied.  It does
-- not manufacture either S_sub or S_Hess.
--
-- Repository search found no independent theorem-bearing inhabitant of either
-- quantitative estimate under the later aliases.  This owner therefore keeps
-- both as physical/source payments and does not collapse them by status.
--
-- This is a frontier refinement only.  It does not identify the old generic
-- real/Cauchy coefficient with R318's rational selected response; that remains
-- R348 C_attach.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedBoundaryFrontierRound347Exact as R347
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104

------------------------------------------------------------------------
-- Minimal source-specific acquisition cut below R347.
------------------------------------------------------------------------

record SelectedSubstitutionHessianAcquisition : Set₁ where
  constructor selected-substitution-hessian-acquisition
  field
    -- Quantitative displacement of the literal CMP116 substituted background
    -- under the selected marked boundary variables.
    SelectedSubstitutedBackgroundControl : Set
    selectedSubstitutedBackgroundControl : SelectedSubstitutedBackgroundControl

    -- Quantitative Lipschitz control for the literal differentiated local
    -- activity Hessian along those substituted backgrounds, on the same domain.
    SelectedLocalActivityHessianStability : Set
    selectedLocalActivityHessianStability : SelectedLocalActivityHessianStability

open SelectedSubstitutionHessianAcquisition public

selectedSubstitutedBackgroundControlLevel : ProofLevel
selectedSubstitutedBackgroundControlLevel = conditional

selectedLocalActivityHessianStabilityLevel : ProofLevel
selectedLocalActivityHessianStabilityLevel = conditional

-- The generic boundary/Cauchy consumer is already represented through the
-- canonical R347 frontier; no import of the older generic-real authority is
-- required here.
selectedBoundaryCompilerLevel : ProofLevel
selectedBoundaryCompilerLevel = R347.genericBoundaryToCauchyLiftLevel

-- Common radius/domain existence is not rescheduled as a fresh analytic leaf.
canonicalCommonRadiusCompilerLevel : ProofLevel
canonicalCommonRadiusCompilerLevel = R104.cmp116CanonicalCommonRadiusCompilerLevel

------------------------------------------------------------------------
-- Pareto / WrongType boundaries.
------------------------------------------------------------------------

record Round350Boundary : Set where
  constructor round350-boundary
  field
    commonDomainExistenceIsFreshSelectedLocalizationAnalysis : Bool
    commonDomainExistenceIsFreshSelectedLocalizationAnalysisIsFalse :
      commonDomainExistenceIsFreshSelectedLocalizationAnalysis ≡ false

    genericCauchyExtractionIsFreshSelectedLocalizationAnalysis : Bool
    genericCauchyExtractionIsFreshSelectedLocalizationAnalysisIsFalse :
      genericCauchyExtractionIsFreshSelectedLocalizationAnalysis ≡ false

    substitutedBackgroundQuantitativeControlStillProofBearing : Bool
    substitutedBackgroundQuantitativeControlStillProofBearingIsTrue :
      substitutedBackgroundQuantitativeControlStillProofBearing ≡ true

    localActivityHessianStabilityStillProofBearing : Bool
    localActivityHessianStabilityStillProofBearingIsTrue :
      localActivityHessianStabilityStillProofBearing ≡ true

    coefficientSameObjectAttachmentStillSeparate : Bool
    coefficientSameObjectAttachmentStillSeparateIsTrue :
      coefficientSameObjectAttachmentStillSeparate ≡ true

    distanceTimeMeaningStillSeparate : Bool
    distanceTimeMeaningStillSeparateIsTrue :
      distanceTimeMeaningStillSeparate ≡ true

canonicalRound350Boundary : Round350Boundary
canonicalRound350Boundary =
  round350-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl

markedSubstitutionCompilerOwned : Bool
markedSubstitutionCompilerOwned = true

markedSubstitutionCompilerOwnedIsTrue :
  markedSubstitutionCompilerOwned ≡ true
markedSubstitutionCompilerOwnedIsTrue = refl

round350FrontierRefinementLevel : ProofLevel
round350FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
