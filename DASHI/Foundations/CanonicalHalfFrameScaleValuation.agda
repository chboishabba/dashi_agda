module DASHI.Foundations.CanonicalHalfFrameScaleValuation where

open import DASHI.Core.Prelude

import DASHI.Foundations.RepresentationChartInvariant as Rep

open Rep.FramedScaleValuationObject

------------------------------------------------------------------------
-- Canonical concrete instance of the unified X/R/C/E/T/S/V carrier.
--
-- The chart changes the presentation role but not the rational point carried
-- by a HalfPresentation.  Scale and valuation are exposed here as the positive
-- denominator and numerator coordinates of the selected presentation.
------------------------------------------------------------------------

canonicalHalfFrameScaleValuation :
  Rep.FramedScaleValuationObject
    Rep.RatioRepresentation
    Rep.HalfPresentation
    Rep.PresentationChart
    Nat
    Nat
canonicalHalfFrameScaleValuation = record
  { evaluate = λ chart presentation → Rep.presentationRatio presentation
  ; transition = λ source target presentation → presentation
  ; transitionPreservesEvaluation = λ source target presentation → refl
  ; transitionIdentity = λ chart presentation → refl
  ; transitionComposition = λ first second third presentation → refl
  ; activeChart = Rep.presentationChart
  ; scaleOf = λ presentation →
      Rep.denominator (Rep.presentationRatio presentation)
  ; valuationOf = λ presentation →
      Rep.numerator (Rep.presentationRatio presentation)
  }

canonicalInspectionValue :
  ∀ presentation →
  proj₁
    (Rep.inspectRepresentation
      canonicalHalfFrameScaleValuation
      presentation)
  ≡ Rep.presentationRatio presentation
canonicalInspectionValue presentation = refl

canonicalInspectionChart :
  ∀ presentation →
  proj₁
    (proj₂
      (Rep.inspectRepresentation
        canonicalHalfFrameScaleValuation
        presentation))
  ≡ Rep.presentationChart presentation
canonicalInspectionChart presentation = refl

canonicalInspectionScale :
  ∀ presentation →
  proj₁
    (proj₂
      (proj₂
        (Rep.inspectRepresentation
          canonicalHalfFrameScaleValuation
          presentation)))
  ≡ Rep.denominator (Rep.presentationRatio presentation)
canonicalInspectionScale presentation = refl

canonicalInspectionValuation :
  ∀ presentation →
  proj₂
    (proj₂
      (proj₂
        (Rep.inspectRepresentation
          canonicalHalfFrameScaleValuation
          presentation)))
  ≡ Rep.numerator (Rep.presentationRatio presentation)
canonicalInspectionValuation presentation = refl

canonicalThreeSixInspectionValue :
  proj₁
    (Rep.inspectRepresentation
      canonicalHalfFrameScaleValuation
      Rep.displayedThreeSix)
  ≡ Rep.threeSix
canonicalThreeSixInspectionValue = refl

canonicalFiftyPercentInspectionValue :
  proj₁
    (Rep.inspectRepresentation
      canonicalHalfFrameScaleValuation
      Rep.displayedFiftyPercent)
  ≡ Rep.fiftyHundredths
canonicalFiftyPercentInspectionValue = refl
