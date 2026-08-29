module DASHI.Programmes.GrokkingValidationCorrectionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- BIDI cut for DASHIg.
--
-- Approximate curve fit on a finite architecture/parameter slice is empirical
-- evidence.  The theorem-facing object is a family law carrying the normalized
-- trajectory identity for every admitted member of the declared family.
------------------------------------------------------------------------

record NormalizedTrajectoryFamily
    (Member Time Accuracy : Set) : Set₁ where
  constructor normalizedTrajectoryFamily
  field
    normalizedTrajectory : Member → Time → Accuracy
    referenceCurve : Time → Accuracy

open NormalizedTrajectoryFamily public

ExactSharedFamilyLaw :
  ∀ {Member Time Accuracy : Set} →
  NormalizedTrajectoryFamily Member Time Accuracy → Set
ExactSharedFamilyLaw family =
  (member : _) → (time : _) →
  normalizedTrajectory family member time ≡ referenceCurve family time

record HeldOutFamilyExtension
    {Member Time Accuracy : Set}
    (family : NormalizedTrajectoryFamily Member Time Accuracy)
    (Baseline HeldOut : Member → Set) : Set₁ where
  constructor heldOutFamilyExtension
  field
    baselineLaw :
      (member : Member) → Baseline member →
      (time : Time) →
      normalizedTrajectory family member time ≡ referenceCurve family time

    heldOutLaw :
      (member : Member) → HeldOut member →
      (time : Time) →
      normalizedTrajectory family member time ≡ referenceCurve family time

open HeldOutFamilyExtension public

combinedFamilyLaw :
  ∀ {Member Time Accuracy : Set}
    {family : NormalizedTrajectoryFamily Member Time Accuracy}
    {Baseline HeldOut : Member → Set} →
  HeldOutFamilyExtension family Baseline HeldOut →
  (member : Member) →
  Baseline member ⊎ HeldOut member →
  (time : Time) →
  normalizedTrajectory family member time ≡ referenceCurve family time
combinedFamilyLaw extension member (inj₁ baseline) time =
  baselineLaw extension member baseline time
combinedFamilyLaw extension member (inj₂ heldOut) time =
  heldOutLaw extension member heldOut time

------------------------------------------------------------------------
-- Runtime failures are a separate evidence class.  They cannot witness a
-- trajectory-family law unless the semantic observation itself is established
-- on a supported execution path.
------------------------------------------------------------------------

record GrokkingValidationCorrectionBoundary : Set where
  constructor grokkingValidationCorrectionBoundary
  field
    lowMSEFitIsExactFamilyIdentity : Bool
    lowMSEFitIsExactFamilyIdentityIsFalse :
      lowMSEFitIsExactFamilyIdentity ≡ false

    twoPointPerfectTimingFitIsUniversalLaw : Bool
    twoPointPerfectTimingFitIsUniversalLawIsFalse :
      twoPointPerfectTimingFitIsUniversalLaw ≡ false

    unsupportedGPUFailureIsModelSemanticsEvidence : Bool
    unsupportedGPUFailureIsModelSemanticsEvidenceIsFalse :
      unsupportedGPUFailureIsModelSemanticsEvidence ≡ false

    heldOutExactReceiptMayExtendFamily : Bool
    heldOutExactReceiptMayExtendFamilyIsTrue :
      heldOutExactReceiptMayExtendFamily ≡ true

canonicalGrokkingValidationCorrectionBoundary :
  GrokkingValidationCorrectionBoundary
canonicalGrokkingValidationCorrectionBoundary =
  grokkingValidationCorrectionBoundary
    false refl
    false refl
    false refl
    true refl
