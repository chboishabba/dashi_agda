{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedSubstitutionHessianCutRound350Exact where

------------------------------------------------------------------------
-- ROUND350 / SPLIT R347 BOUNDARY COMPARISON AT THE EXISTING GENERIC ABI
--
-- `BalabanDecoupledActivityHessian.markedSubstitutionStabilityLiftsToCoefficient`
-- already proves the generic implication that motivates this cut:
--
--   selected Hessian stability against substitutionDistance
-- + selected substitutionDistance <= markedInput
-- ---------------------------------------------------------
--   marked Cauchy/Hessian coefficient <= lipschitz * markedInput.
--
-- Hence pointwise boundary/Cauchy extraction is not a primitive YM leaf.  The
-- source-specific physical application splits into exactly two inputs:
--
--   H_stab:
--     selected boundary Hessian-integrand difference
--       <= lipschitz * selected substitutionDistance;
--
--   H_sub:
--     selected substitutionDistance <= selected markedInput.
--
-- Both are on the literal selected CMP116 substituted-background carrier.
-- Common-domain existence/smallness and generic Cauchy bookkeeping are already
-- separated by earlier owners; neither quantitative source estimate is created
-- by those compilers.
--
-- Independent leaves remain R348 C_attach and R346 D_time.  This owner records
-- the dependency cut only; neither H_stab nor H_sub is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedBoundaryFrontierRound347Exact as R347
import DASHI.Physics.YangMills.BalabanCMP116SelectedCoefficientAttachmentRound348Exact as R348
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104

------------------------------------------------------------------------
-- Existing compiler/admissibility surfaces already owned.
------------------------------------------------------------------------

genericSubstitutionToCoefficientCompilerLevel : ProofLevel
genericSubstitutionToCoefficientCompilerLevel =
  Source.markedBoundaryToHessianCauchyLiftLevel

canonicalCommonRadiusCompilerLevel : ProofLevel
canonicalCommonRadiusCompilerLevel = R104.cmp116CanonicalCommonRadiusCompilerLevel

------------------------------------------------------------------------
-- Remaining source-specific physical inputs.
------------------------------------------------------------------------

-- H_stab: on the selected boundary assignment, varying the nonlinear
-- substituted background changes the twice-varied local activity by at most a
-- nonnegative Lipschitz factor times the substitution distance.
selectedHessianStabilityLevel : ProofLevel
selectedHessianStabilityLevel = conditional

-- H_sub: the selected nonlinear substituted-background distance is controlled by
-- the actual marked input/shell coordinate used by the shared Hessian mark.
selectedSubstitutionMarkedLevel : ProofLevel
selectedSubstitutionMarkedLevel = conditional

-- R348's scalar same-object coefficient attachment is not implied by these
-- analytic inequalities and remains independent.
selectedCoefficientAttachmentLevel : ProofLevel
selectedCoefficientAttachmentLevel = R348.selectedCoefficientSameObjectLevel

-- The parent R347 physical boundary leaf is exactly the consumer these two
-- estimates are intended to inhabit after physical/source instantiation.
selectedBoundaryParentLevel : ProofLevel
selectedBoundaryParentLevel = R347.selectedMarkedBoundarySubstitutionLevel

------------------------------------------------------------------------
-- Pareto firewalls.
------------------------------------------------------------------------

freshCauchyCoefficientAnalysisRequired : Bool
freshCauchyCoefficientAnalysisRequired = false

freshCauchyCoefficientAnalysisRequiredIsFalse :
  freshCauchyCoefficientAnalysisRequired ≡ false
freshCauchyCoefficientAnalysisRequiredIsFalse = refl

freshBoundaryEnvelopeTheoremRequired : Bool
freshBoundaryEnvelopeTheoremRequired = false

freshBoundaryEnvelopeTheoremRequiredIsFalse :
  freshBoundaryEnvelopeTheoremRequired ≡ false
freshBoundaryEnvelopeTheoremRequiredIsFalse = refl

commonDomainExistenceStillPrimitiveHere : Bool
commonDomainExistenceStillPrimitiveHere = false

commonDomainExistenceStillPrimitiveHereIsFalse :
  commonDomainExistenceStillPrimitiveHere ≡ false
commonDomainExistenceStillPrimitiveHereIsFalse = refl

selectedCoefficientAttachmentStillIndependent : Bool
selectedCoefficientAttachmentStillIndependent = true

selectedCoefficientAttachmentStillIndependentIsTrue :
  selectedCoefficientAttachmentStillIndependent ≡ true
selectedCoefficientAttachmentStillIndependentIsTrue = refl

selectedDistanceTimeStillIndependent : Bool
selectedDistanceTimeStillIndependent = true

selectedDistanceTimeStillIndependentIsTrue :
  selectedDistanceTimeStillIndependent ≡ true
selectedDistanceTimeStillIndependentIsTrue = refl

record Round350Boundary : Set where
  constructor round350-boundary
  field
    substitutionCauchyCompilerOwned : Bool
    substitutionCauchyCompilerOwnedIsTrue :
      substitutionCauchyCompilerOwned ≡ true

    commonDomainCompilerOwned : Bool
    commonDomainCompilerOwnedIsTrue : commonDomainCompilerOwned ≡ true

    selectedHessianStabilityStillPhysical : Bool
    selectedHessianStabilityStillPhysicalIsTrue :
      selectedHessianStabilityStillPhysical ≡ true

    selectedSubstitutionMarkedStillPhysical : Bool
    selectedSubstitutionMarkedStillPhysicalIsTrue :
      selectedSubstitutionMarkedStillPhysical ≡ true

    coefficientAttachmentRemainsSeparate : Bool
    coefficientAttachmentRemainsSeparateIsTrue :
      coefficientAttachmentRemainsSeparate ≡ true

canonicalRound350Boundary : Round350Boundary
canonicalRound350Boundary =
  round350-boundary
    true refl
    true refl
    true refl
    true refl
    true refl

round350FrontierRefinementLevel : ProofLevel
round350FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
