module DASHI.Programmes.GrokkingHeldOutToleranceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- BIDI empirical consumer for dashifine / DASHIg.
--
-- Exact curve identity remains a valid theorem ceiling, but finite numerical
-- learning experiments should normally target a declared closeness relation
-- rather than definitional equality.  The relation is consumer-owned: the
-- experiment does not get to manufacture scientific authority by choosing a
-- tolerance after seeing the result.
------------------------------------------------------------------------

record ApproximateTrajectoryFamily
    (Member Time Accuracy : Set) : Set₁ where
  constructor approximateTrajectoryFamily
  field
    trajectory : Member → Time → Accuracy
    referenceCurve : Time → Accuracy
    Close : Accuracy → Accuracy → Set

open ApproximateTrajectoryFamily public

ApproximateFamilyLaw :
  ∀ {Member Time Accuracy : Set} →
  ApproximateTrajectoryFamily Member Time Accuracy → Set
ApproximateFamilyLaw family =
  (member : _) → (time : _) →
  Close family
    (trajectory family member time)
    (referenceCurve family time)

record HeldOutApproximateExtension
    {Member Time Accuracy : Set}
    (family : ApproximateTrajectoryFamily Member Time Accuracy)
    (Baseline HeldOut : Member → Set) : Set₁ where
  constructor heldOutApproximateExtension
  field
    baselineLaw :
      (member : Member) → Baseline member →
      (time : Time) →
      Close family
        (trajectory family member time)
        (referenceCurve family time)

    heldOutLaw :
      (member : Member) → HeldOut member →
      (time : Time) →
      Close family
        (trajectory family member time)
        (referenceCurve family time)

open HeldOutApproximateExtension public

combinedApproximateFamilyLaw :
  ∀ {Member Time Accuracy : Set}
    {family : ApproximateTrajectoryFamily Member Time Accuracy}
    {Baseline HeldOut : Member → Set} →
  HeldOutApproximateExtension family Baseline HeldOut →
  (member : Member) →
  Baseline member ⊎ HeldOut member →
  (time : Time) →
  Close family
    (trajectory family member time)
    (referenceCurve family time)
combinedApproximateFamilyLaw extension member (inj₁ baseline) time =
  baselineLaw extension member baseline time
combinedApproximateFamilyLaw extension member (inj₂ heldOut) time =
  heldOutLaw extension member heldOut time

------------------------------------------------------------------------
-- Criterion provenance.
--
-- `Close` is mathematically just a relation.  A scientifically promoted use of
-- it additionally needs a receipt that the relation/tolerance was fixed for the
-- downstream consumer independently of the held-out result.
------------------------------------------------------------------------

record ClosenessCriterionReceipt
    {Accuracy : Set}
    (Close : Accuracy → Accuracy → Set) : Set₁ where
  constructor closenessCriterionReceipt
  field
    criterionDeclaredBeforeHeldOutEvaluation : Set
    criterionJustification : Set

open ClosenessCriterionReceipt public

record GrokkingHeldOutToleranceBoundary : Set where
  constructor grokkingHeldOutToleranceBoundary
  field
    finiteNumericalStudyRequiresDefinitionalCurveEquality : Bool
    finiteNumericalStudyRequiresDefinitionalCurveEqualityIsFalse :
      finiteNumericalStudyRequiresDefinitionalCurveEquality ≡ false

    postHocToleranceIsIndependentValidation : Bool
    postHocToleranceIsIndependentValidationIsFalse :
      postHocToleranceIsIndependentValidation ≡ false

    declaredClosenessPlusHeldOutReceiptCanSupportFamilyClaim : Bool
    declaredClosenessPlusHeldOutReceiptCanSupportFamilyClaimIsTrue :
      declaredClosenessPlusHeldOutReceiptCanSupportFamilyClaim ≡ true

canonicalGrokkingHeldOutToleranceBoundary :
  GrokkingHeldOutToleranceBoundary
canonicalGrokkingHeldOutToleranceBoundary =
  grokkingHeldOutToleranceBoundary
    false refl
    false refl
    true refl
