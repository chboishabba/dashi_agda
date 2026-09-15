{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedHessianStabilitySourceRound352Exact where

------------------------------------------------------------------------
-- ROUND352 / H_stab IS SOURCE LOCAL STABILITY + SAME-OBJECT ATTACHMENT
--
-- R350 isolates
--
--   H_stab : hessianDifference <= lipschitz * substitutionDistance.
--
-- Existing local-Hessian/Lipschitz machinery in the Wilson/coercivity lane has
-- the same scalar algebraic shape, but it is not the CMP116 substituted local
-- activity appearing in the selected R318/R350 consumer.  It is therefore a
-- donor/calibration only, not proof payment.
--
-- The least-privilege BIDI cut is:
--
--   source acquisition:
--     literal CMP109/CMP116 local twice-varied activity stability
--       Hdiff^src <= L^src * d_sub^src
--
--   same-object attachment:
--     Hdiff^selected = Hdiff^src
--     L^selected = L^src
--     d_sub^selected = d_sub^src
--
--   compiler:
--     Hdiff^selected <= L^selected * d_sub^selected.
--
-- This file proves only equality transport.  It does not manufacture the
-- source local-stability estimate or its selected-carrier interpretation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact as Marked
import DASHI.Physics.YangMills.BalabanYM4UniformCoercivityPerturbationExact as Coercivity
import DASHI.Physics.YangMills.BalabanYM4PlaquetteHessianOverlapExact as Plaquette
import DASHI.Physics.YangMills.BalabanSelectedSubstitutionHessianCutRound350Exact as R350

------------------------------------------------------------------------
-- Source theorem ABI.
------------------------------------------------------------------------

record CMP116LocalHessianStabilitySource (BoundaryPoint : Set) : Set₁ where
  field
    sourceHessianDifference : BoundaryPoint → ℝ
    sourceLipschitz : ℝ
    sourceSubstitutionDistance : BoundaryPoint → ℝ

    sourceHessianStable : ∀ point →
      sourceHessianDifference point
        ≤ℝ sourceLipschitz *ℝ sourceSubstitutionDistance point

open CMP116LocalHessianStabilitySource public

------------------------------------------------------------------------
-- Selected R350 attachment.
------------------------------------------------------------------------

record SelectedHessianStabilityAttachment
    {BoundaryPoint : Set}
    (source : CMP116LocalHessianStabilitySource BoundaryPoint) : Set₁ where
  field
    selectedHessianDifference : BoundaryPoint → ℝ
    selectedLipschitz : ℝ
    selectedSubstitutionDistance : BoundaryPoint → ℝ

    selectedHessianDifferenceIsSource : ∀ point →
      selectedHessianDifference point ≡ sourceHessianDifference source point

    selectedLipschitzIsSource :
      selectedLipschitz ≡ sourceLipschitz source

    selectedSubstitutionDistanceIsSource : ∀ point →
      selectedSubstitutionDistance point
        ≡ sourceSubstitutionDistance source point

open SelectedHessianStabilityAttachment public

selectedHessianStabilityFromSource :
  ∀ {BoundaryPoint}
    (source : CMP116LocalHessianStabilitySource BoundaryPoint)
    (attachment : SelectedHessianStabilityAttachment source)
    point →
  selectedHessianDifference attachment point
    ≤ℝ selectedLipschitz attachment
      *ℝ selectedSubstitutionDistance attachment point
selectedHessianStabilityFromSource source attachment point
  rewrite selectedHessianDifferenceIsSource attachment point
  | selectedLipschitzIsSource attachment
  | selectedSubstitutionDistanceIsSource attachment point =
  sourceHessianStable source point

------------------------------------------------------------------------
-- Source / application / compiler accounting.
------------------------------------------------------------------------

-- CMP116 source authority already says finite declared derivatives retain the
-- common analytic/localized structure.  It does not by itself instantiate this
-- quantitative local Lipschitz theorem on the selected substituted backgrounds.
cmp116FiniteDerivativeAnalyticityAuthorityLevel : ProofLevel
cmp116FiniteDerivativeAnalyticityAuthorityLevel =
  CMP116.cmp116DifferentiatedActivityLocalizationLevel

-- CMP109/CMP99 own marked differentiated-response/domain-comparison decay, but
-- selected R350 H_stab still needs theorem-bearing identification with this
-- local substituted-background stability surface.
cmp109MarkedDifferentiatedResponseAuthorityLevel : ProofLevel
cmp109MarkedDifferentiatedResponseAuthorityLevel =
  Marked.cmp109DifferentiatedMarkedActivityDecayLevel

literalCMP116LocalHessianStabilitySourceLevel : ProofLevel
literalCMP116LocalHessianStabilitySourceLevel = conditional

selectedR318R350HessianStabilityAttachmentLevel : ProofLevel
selectedR318R350HessianStabilityAttachmentLevel = conditional

selectedHessianStabilityTransportCompilerLevel : ProofLevel
selectedHessianStabilityTransportCompilerLevel = machineChecked

r350ParentHStabLevel : ProofLevel
r350ParentHStabLevel = R350.selectedHessianStabilityLevel

------------------------------------------------------------------------
-- Wrong-carrier donor firewalls.
------------------------------------------------------------------------

-- Round53 Wilson/coercivity local-Hessian Lipschitz and plaquette-overlap
-- machinery is useful calibration, but its carrier is not the CMP116 localized
-- substituted activity consumed by R350.
wilsonCoercivityLocalLipschitzDonorLevel : ProofLevel
wilsonCoercivityLocalLipschitzDonorLevel =
  Coercivity.ym4PhysicalLocalHessianRadiusBudgetLevel

plaquetteOverlapCompilerDonorLevel : ProofLevel
plaquetteOverlapCompilerDonorLevel = Plaquette.ym4PlaquetteHessianOverlapLevel

wilsonCoercivityDirectlyPaysHStab : Bool
wilsonCoercivityDirectlyPaysHStab = false

wilsonCoercivityDirectlyPaysHStabIsFalse :
  wilsonCoercivityDirectlyPaysHStab ≡ false
wilsonCoercivityDirectlyPaysHStabIsFalse = refl

cmp116AnalyticityStatusDirectlyPaysHStab : Bool
cmp116AnalyticityStatusDirectlyPaysHStab = false

cmp116AnalyticityStatusDirectlyPaysHStabIsFalse :
  cmp116AnalyticityStatusDirectlyPaysHStab ≡ false
cmp116AnalyticityStatusDirectlyPaysHStabIsFalse = refl

------------------------------------------------------------------------
-- BIDI / Pareto boundary.
------------------------------------------------------------------------

sourceStabilityAndSelectedAttachmentAreDistinct : Bool
sourceStabilityAndSelectedAttachmentAreDistinct = true

sourceStabilityAndSelectedAttachmentAreDistinctIsTrue :
  sourceStabilityAndSelectedAttachmentAreDistinct ≡ true
sourceStabilityAndSelectedAttachmentAreDistinctIsTrue = refl

freshBoundaryEnvelopeAnalysisRequired : Bool
freshBoundaryEnvelopeAnalysisRequired = false

freshBoundaryEnvelopeAnalysisRequiredIsFalse :
  freshBoundaryEnvelopeAnalysisRequired ≡ false
freshBoundaryEnvelopeAnalysisRequiredIsFalse = refl

record Round352Boundary : Set where
  constructor round352-boundary
  field
    sourceLocalStabilityStillPhysical : Bool
    sourceLocalStabilityStillPhysicalIsTrue :
      sourceLocalStabilityStillPhysical ≡ true

    selectedAttachmentStillPhysical : Bool
    selectedAttachmentStillPhysicalIsTrue :
      selectedAttachmentStillPhysical ≡ true

    equalityTransportCompilerOwned : Bool
    equalityTransportCompilerOwnedIsTrue :
      equalityTransportCompilerOwned ≡ true

    oldWilsonLipschitzIsNotDirectPayment : Bool
    oldWilsonLipschitzIsNotDirectPaymentIsTrue :
      oldWilsonLipschitzIsNotDirectPayment ≡ true

canonicalRound352Boundary : Round352Boundary
canonicalRound352Boundary =
  round352-boundary
    true refl
    true refl
    true refl
    true refl

round352FrontierRefinementLevel : ProofLevel
round352FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
