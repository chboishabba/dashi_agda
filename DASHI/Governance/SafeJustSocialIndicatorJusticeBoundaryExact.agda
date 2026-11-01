module DASHI.Governance.SafeJustSocialIndicatorJusticeBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Governance.SafeJustIndicatorSystemExact as Indicators

------------------------------------------------------------------------
-- MEASURED SOCIAL THRESHOLDS != EXHAUSTIVE PARTICIPATORY JUSTICE
--
-- The eleven O'Neill/Fanning social indicators are an empirical observer for a
-- declared consumer.  Satisfying every measured threshold is not promoted into
-- a universal certificate of recognition, representation, legitimacy or
-- participatory justice.  After ancestry reconciliation this is intended to be
-- a thin consumer of the Fraser-style axis separation on #620.
------------------------------------------------------------------------

allMeasuredSocialThresholds : Indicators.SocialProfile
allMeasuredSocialThresholds =
  Indicators.socialProfile
    true true true true true true true true true true true

allMeasuredThresholdsAreMet :
  Indicators.allSocialMet allMeasuredSocialThresholds ≡ true
allMeasuredThresholdsAreMet = refl

data ParticipatoryJusticeCertificate : Set where

data RecognitionClosureCertificate : Set where

data RepresentationClosureCertificate : Set where

data LegitimacyClosureCertificate : Set where

allMeasuredThresholdsDoNotSupplyParticipatoryJustice :
  ParticipatoryJusticeCertificate → ⊥
allMeasuredThresholdsDoNotSupplyParticipatoryJustice ()

allMeasuredThresholdsDoNotSupplyRecognitionClosure :
  RecognitionClosureCertificate → ⊥
allMeasuredThresholdsDoNotSupplyRecognitionClosure ()

allMeasuredThresholdsDoNotSupplyRepresentationClosure :
  RepresentationClosureCertificate → ⊥
allMeasuredThresholdsDoNotSupplyRepresentationClosure ()

allMeasuredThresholdsDoNotSupplyLegitimacyClosure :
  LegitimacyClosureCertificate → ⊥
allMeasuredThresholdsDoNotSupplyLegitimacyClosure ()

record SocialIndicatorJusticeBoundary : Set where
  constructor socialIndicatorJusticeBoundary
  field
    measuredSocialThresholdsAreDeclaredEmpiricalSurface : Bool
    measuredSocialThresholdsAreDeclaredEmpiricalSurfaceIsTrue :
      measuredSocialThresholdsAreDeclaredEmpiricalSurface ≡ true
    allMeasuredThresholdsImplyParticipatoryJustice : Bool
    allMeasuredThresholdsImplyParticipatoryJusticeIsFalse :
      allMeasuredThresholdsImplyParticipatoryJustice ≡ false
    allMeasuredThresholdsImplyRepresentationClosure : Bool
    allMeasuredThresholdsImplyRepresentationClosureIsFalse :
      allMeasuredThresholdsImplyRepresentationClosure ≡ false
    allMeasuredThresholdsImplyLegitimacyClosure : Bool
    allMeasuredThresholdsImplyLegitimacyClosureIsFalse :
      allMeasuredThresholdsImplyLegitimacyClosure ≡ false

canonicalSocialIndicatorJusticeBoundary : SocialIndicatorJusticeBoundary
canonicalSocialIndicatorJusticeBoundary =
  socialIndicatorJusticeBoundary true refl false refl false refl false refl
