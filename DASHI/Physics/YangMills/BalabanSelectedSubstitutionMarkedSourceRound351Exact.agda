{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedSubstitutionMarkedSourceRound351Exact where

------------------------------------------------------------------------
-- ROUND351 / H_sub IS SOURCE DISPLACEMENT + SAME-OBJECT ATTACHMENT
--
-- R350 isolates
--
--   H_sub : substitutionDistance <= markedInput.
--
-- The CMP99/CMP109 marked domain-comparison machinery is a donor for the
-- EFFECT of a background/domain discrepancy on differentiated activities; it
-- is not itself the prior geometric statement that the substituted-background
-- displacement is bounded by the selected mark.  Do not collapse those two
-- coordinates.
--
-- The consumer-minimal BIDI cut is therefore:
--
--   source acquisition:
--     literal CMP116 substituted-background displacement theorem
--       d_sub^src <= M_marked^src
--
--   same-object attachment:
--     d_sub^selected = d_sub^src
--     M_marked^selected = M_marked^src
--
--   compiler:
--     d_sub^selected <= M_marked^selected.
--
-- This file proves only the equality transport compiler.  It does not invent
-- the source displacement theorem or the selected-carrier attachment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact as CMP99
import DASHI.Physics.YangMills.BalabanSelectedSubstitutionHessianCutRound350Exact as R350

------------------------------------------------------------------------
-- Source theorem ABI.
------------------------------------------------------------------------

record CMP116SubstitutionMarkedSource (BoundaryPoint : Set) : Set₁ where
  field
    sourceSubstitutionDistance : BoundaryPoint → ℝ
    sourceMarkedInput : ℝ

    sourceDistanceNonnegative : ∀ point →
      0ℝ ≤ℝ sourceSubstitutionDistance point

    sourceMarkedInputNonnegative :
      0ℝ ≤ℝ sourceMarkedInput

    sourceSubstitutionMarked : ∀ point →
      sourceSubstitutionDistance point ≤ℝ sourceMarkedInput

open CMP116SubstitutionMarkedSource public

------------------------------------------------------------------------
-- Selected R350 attachment.
------------------------------------------------------------------------

record SelectedSubstitutionMarkedAttachment
    {BoundaryPoint : Set}
    (source : CMP116SubstitutionMarkedSource BoundaryPoint) : Set₁ where
  field
    selectedSubstitutionDistance : BoundaryPoint → ℝ
    selectedMarkedInput : ℝ

    selectedDistanceIsSource : ∀ point →
      selectedSubstitutionDistance point
      ≡ sourceSubstitutionDistance source point

    selectedMarkedInputIsSource :
      selectedMarkedInput ≡ sourceMarkedInput source

open SelectedSubstitutionMarkedAttachment public

selectedSubstitutionMarkedFromSource :
  ∀ {BoundaryPoint}
    (source : CMP116SubstitutionMarkedSource BoundaryPoint)
    (attachment : SelectedSubstitutionMarkedAttachment source)
    point →
  selectedSubstitutionDistance attachment point
    ≤ℝ selectedMarkedInput attachment
selectedSubstitutionMarkedFromSource source attachment point
  rewrite selectedDistanceIsSource attachment point
  | selectedMarkedInputIsSource attachment =
  sourceSubstitutionMarked source point

------------------------------------------------------------------------
-- Source / application / compiler accounting.
------------------------------------------------------------------------

-- CMP116 owns the nonlinear substituted-background analytic construction on its
-- declared domain.  The exact quantitative source displacement inequality above
-- still requires proof-bearing extraction/replay on that source carrier.
cmp116SubstitutedBackgroundConstructionAuthorityLevel : ProofLevel
cmp116SubstitutedBackgroundConstructionAuthorityLevel =
  CMP116.cmp116DifferentiatedActivityLocalizationLevel

literalCMP116SubstitutionMarkedSourceLevel : ProofLevel
literalCMP116SubstitutionMarkedSourceLevel = conditional

selectedR318R350SubstitutionAttachmentLevel : ProofLevel
selectedR318R350SubstitutionAttachmentLevel = conditional

selectedSubstitutionMarkedTransportCompilerLevel : ProofLevel
selectedSubstitutionMarkedTransportCompilerLevel = machineChecked

r350ParentHSubLevel : ProofLevel
r350ParentHSubLevel = R350.selectedSubstitutionMarkedLevel

-- CMP99/109 marked decay remains a valuable donor for the differentiated
-- response/Hessian side, but is not a theorem of d_sub <= M_marked.
cmp99MarkedBackgroundDifferenceLevel : ProofLevel
cmp99MarkedBackgroundDifferenceLevel =
  CMP99.cmp99BackgroundPropagatorMarkedDifferenceLevel

cmp99DirectlyPaysHSub : Bool
cmp99DirectlyPaysHSub = false

cmp99DirectlyPaysHSubIsFalse : cmp99DirectlyPaysHSub ≡ false
cmp99DirectlyPaysHSubIsFalse = refl

------------------------------------------------------------------------
-- BIDI / Pareto boundary.
------------------------------------------------------------------------

sourceAcquisitionAndSelectedAttachmentAreDistinct : Bool
sourceAcquisitionAndSelectedAttachmentAreDistinct = true

sourceAcquisitionAndSelectedAttachmentAreDistinctIsTrue :
  sourceAcquisitionAndSelectedAttachmentAreDistinct ≡ true
sourceAcquisitionAndSelectedAttachmentAreDistinctIsTrue = refl

freshCauchyAnalysisRequired : Bool
freshCauchyAnalysisRequired = false

freshCauchyAnalysisRequiredIsFalse : freshCauchyAnalysisRequired ≡ false
freshCauchyAnalysisRequiredIsFalse = refl

record Round351Boundary : Set where
  constructor round351-boundary
  field
    sourceDisplacementStillPhysical : Bool
    sourceDisplacementStillPhysicalIsTrue :
      sourceDisplacementStillPhysical ≡ true

    selectedAttachmentStillPhysical : Bool
    selectedAttachmentStillPhysicalIsTrue :
      selectedAttachmentStillPhysical ≡ true

    equalityTransportCompilerOwned : Bool
    equalityTransportCompilerOwnedIsTrue :
      equalityTransportCompilerOwned ≡ true

    cmp99IsNotDirectHSubPayment : Bool
    cmp99IsNotDirectHSubPaymentIsTrue :
      cmp99IsNotDirectHSubPayment ≡ true

canonicalRound351Boundary : Round351Boundary
canonicalRound351Boundary =
  round351-boundary
    true refl
    true refl
    true refl
    true refl

round351FrontierRefinementLevel : ProofLevel
round351FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
