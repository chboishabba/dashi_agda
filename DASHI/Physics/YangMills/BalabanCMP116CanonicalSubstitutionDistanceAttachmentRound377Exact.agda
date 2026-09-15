module DASHI.Physics.YangMills.BalabanCMP116CanonicalSubstitutionDistanceAttachmentRound377Exact where

------------------------------------------------------------------------
-- ROUND377 / ONE SUBSTITUTION-DISTANCE COORDINATE, NOT TWO WELDS
--
-- R351's selected attachment and R376's BIDI bridge historically exposed two
-- equalities around the same physical quantity:
--
--   selected R351 distance = source R351 distance,
--   R373 boundary distance = selected R351 distance.
--
-- The second equality is representation debt.  The current direct route already
-- has the R373 boundary distance as its live selected coordinate.  Define the
-- R351 selected distance to BE that coordinate, and define its selected marked
-- input to be the source marked input.  Then R376's boundary-distance weld and
-- the marked-input identity are refl.
--
-- The sole physical/same-object payment is therefore:
--
--   R373.selectedBoundarySubstitutionDistance s
--     = R351.sourceSubstitutionDistance source s.
--
-- No displacement inequality is manufactured here; R351.sourceSubstitutionMarked
-- remains the theorem-bearing source payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedSubstitutionMarkedSourceRound351Exact as R351
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373
import DASHI.Physics.YangMills.BalabanCMP116SubstitutionHessianBidiRound376Exact as R376

record CanonicalSubstitutionDistanceAttachmentData : Set₁ where
  field
    joint : R373.JointBoundaryHessianPaymentData
    source : R351.CMP116SubstitutionMarkedSource (R376.JointBoundaryPoint joint)

    -- The only same-object attachment retained by this owner.
    boundaryDistanceIsSourceDistance :
      ∀ s →
      R373.selectedBoundarySubstitutionDistance joint s
      ≡ R351.sourceSubstitutionDistance source s

open CanonicalSubstitutionDistanceAttachmentData public

canonicalR351Attachment :
  (dataSet : CanonicalSubstitutionDistanceAttachmentData) →
  R351.SelectedSubstitutionMarkedAttachment (source dataSet)
canonicalR351Attachment dataSet = record
  { R351.selectedSubstitutionDistance =
      R373.selectedBoundarySubstitutionDistance (joint dataSet)
  ; R351.selectedMarkedInput = R351.sourceMarkedInput (source dataSet)
  ; R351.selectedDistanceIsSource = boundaryDistanceIsSourceDistance dataSet
  ; R351.selectedMarkedInputIsSource = refl
  }

boundaryDistanceIsCanonicalSelectedDistance :
  (dataSet : CanonicalSubstitutionDistanceAttachmentData) →
  ∀ s →
  R373.selectedBoundarySubstitutionDistance (joint dataSet) s
  ≡
  R351.selectedSubstitutionDistance (canonicalR351Attachment dataSet) s
boundaryDistanceIsCanonicalSelectedDistance dataSet s = refl

asRound376 :
  (dataSet : CanonicalSubstitutionDistanceAttachmentData) →
  (selectedLipschitzNonnegative :
    DASHI.Foundations.RealAnalysisAxioms.0ℝ
      DASHI.Foundations.RealAnalysisAxioms.≤ℝ
    R373.selectedLipschitz (joint dataSet)) →
  R376.CMP116SubstitutionHessianBidiData
asRound376 dataSet selectedLipschitzNonnegative = record
  { R376.joint = joint dataSet
  ; R376.substitutionSource = source dataSet
  ; R376.substitutionAttachment = canonicalR351Attachment dataSet
  ; R376.selectedLipschitzNonnegative = selectedLipschitzNonnegative
  ; R376.boundaryDistanceIsSelectedSubstitutionDistance =
      boundaryDistanceIsCanonicalSelectedDistance dataSet
  }

------------------------------------------------------------------------
-- Pareto boundary.
------------------------------------------------------------------------

canonicalDistanceAttachmentCompilerLevel : ProofLevel
canonicalDistanceAttachmentCompilerLevel = machineChecked

literalBoundaryDistanceToSourceDistanceLevel : ProofLevel
literalBoundaryDistanceToSourceDistanceLevel = conditional

secondSelectedDistanceCoordinateRequiredAfterRound377 : Bool
secondSelectedDistanceCoordinateRequiredAfterRound377 = false

secondSelectedDistanceCoordinateRequiredAfterRound377IsFalse :
  secondSelectedDistanceCoordinateRequiredAfterRound377 ≡ false
secondSelectedDistanceCoordinateRequiredAfterRound377IsFalse = refl

r376BoundaryDistanceWeldPrimitiveAfterRound377 : Bool
r376BoundaryDistanceWeldPrimitiveAfterRound377 = false

r376BoundaryDistanceWeldPrimitiveAfterRound377IsFalse :
  r376BoundaryDistanceWeldPrimitiveAfterRound377 ≡ false
r376BoundaryDistanceWeldPrimitiveAfterRound377IsFalse = refl

sourceDisplacementTheoremStillPhysical : Bool
sourceDisplacementTheoremStillPhysical = true

sourceDisplacementTheoremStillPhysicalIsTrue :
  sourceDisplacementTheoremStillPhysical ≡ true
sourceDisplacementTheoremStillPhysicalIsTrue = refl

record Round377Boundary : Set where
  constructor round377-boundary
  field
    oneSelectedDistanceCoordinateFeedsBothRoutes : Bool
    oneSelectedDistanceCoordinateFeedsBothRoutesIsTrue :
      oneSelectedDistanceCoordinateFeedsBothRoutes ≡ true

    onlyDistanceSameObjectWeldIsBoundaryToSource : Bool
    onlyDistanceSameObjectWeldIsBoundaryToSourceIsTrue :
      onlyDistanceSameObjectWeldIsBoundaryToSource ≡ true

    sourceInequalityNotManufacturedByAttachment : Bool
    sourceInequalityNotManufacturedByAttachmentIsTrue :
      sourceInequalityNotManufacturedByAttachment ≡ true

canonicalRound377Boundary : Round377Boundary
canonicalRound377Boundary =
  round377-boundary true refl true refl true refl

round377FrontierRefinementLevel : ProofLevel
round377FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
