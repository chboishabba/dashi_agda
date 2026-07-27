module DASHI.Foundations.CanonicalHalfFrameScaleValuation where

open import DASHI.Core.Prelude

import DASHI.Foundations.RepresentationChartInvariant as Rep

open Rep.FramedScaleValuationObject

------------------------------------------------------------------------
-- Canonical concrete instance of the unified X/R/C/E/T/S/V carrier.
--
-- A representation carries its rational value and active chart explicitly.
-- Transition changes only the chart, so target correctness, evaluation
-- preservation, identity and composition are all kernel-visible.
------------------------------------------------------------------------

record ChartedHalfRepresentation : Set where
  constructor charted-half
  field
    carriedRatio : Rep.RatioRepresentation
    carriedChart : Rep.PresentationChart

open ChartedHalfRepresentation public

chartedPresentation :
  Rep.HalfPresentation →
  ChartedHalfRepresentation
chartedPresentation presentation =
  charted-half
    (Rep.presentationRatio presentation)
    (Rep.presentationChart presentation)

chartedThreeSix : ChartedHalfRepresentation
chartedThreeSix = chartedPresentation Rep.displayedThreeSix

chartedOneHalf : ChartedHalfRepresentation
chartedOneHalf = chartedPresentation Rep.displayedOneHalf

chartedDecimalPointFive : ChartedHalfRepresentation
chartedDecimalPointFive =
  chartedPresentation Rep.displayedDecimalPointFive

chartedFiftyPercent : ChartedHalfRepresentation
chartedFiftyPercent =
  chartedPresentation Rep.displayedFiftyPercent

chartedBinaryPointOne : ChartedHalfRepresentation
chartedBinaryPointOne =
  chartedPresentation Rep.displayedBinaryPointOne

transitionChart :
  Rep.PresentationChart →
  ChartedHalfRepresentation →
  ChartedHalfRepresentation
transitionChart target (charted-half value source) =
  charted-half value target

canonicalHalfFrameScaleValuation :
  Rep.FramedScaleValuationObject
    Rep.RatioRepresentation
    ChartedHalfRepresentation
    Rep.PresentationChart
    Nat
    Nat
canonicalHalfFrameScaleValuation = record
  { evaluate = λ chart representation → carriedRatio representation
  ; activeChart = carriedChart
  ; transition = transitionChart
  ; transitionTargetsChart = λ
      { target (charted-half value source) → refl
      }
  ; transitionPreservesEvaluation = λ
      { target (charted-half value source) → refl
      }
  ; transitionIdentity = λ
      { (charted-half value chart) → refl
      }
  ; transitionComposition = λ
      { second third (charted-half value source) → refl
      }
  ; scaleOf = λ representation →
      Rep.denominator (carriedRatio representation)
  ; valuationOf = λ representation →
      Rep.numerator (carriedRatio representation)
  }

canonicalTransitionTargetsChart :
  ∀ target representation →
  Rep.activeChart canonicalHalfFrameScaleValuation
    (Rep.transition canonicalHalfFrameScaleValuation target representation)
  ≡ target
canonicalTransitionTargetsChart target (charted-half value source) = refl

canonicalTransitionPreservesValue :
  ∀ target representation →
  Rep.evaluate canonicalHalfFrameScaleValuation target
    (Rep.transition canonicalHalfFrameScaleValuation target representation)
  ≡
  Rep.evaluate canonicalHalfFrameScaleValuation
    (Rep.activeChart canonicalHalfFrameScaleValuation representation)
    representation
canonicalTransitionPreservesValue target (charted-half value source) = refl

canonicalInspectionValue :
  ∀ representation →
  proj₁
    (Rep.inspectRepresentation
      canonicalHalfFrameScaleValuation
      representation)
  ≡ carriedRatio representation
canonicalInspectionValue representation = refl

canonicalInspectionChart :
  ∀ representation →
  proj₁
    (proj₂
      (Rep.inspectRepresentation
        canonicalHalfFrameScaleValuation
        representation))
  ≡ carriedChart representation
canonicalInspectionChart representation = refl

canonicalInspectionScale :
  ∀ representation →
  proj₁
    (proj₂
      (proj₂
        (Rep.inspectRepresentation
          canonicalHalfFrameScaleValuation
          representation)))
  ≡ Rep.denominator (carriedRatio representation)
canonicalInspectionScale representation = refl

canonicalInspectionValuation :
  ∀ representation →
  proj₂
    (proj₂
      (proj₂
        (Rep.inspectRepresentation
          canonicalHalfFrameScaleValuation
          representation)))
  ≡ Rep.numerator (carriedRatio representation)
canonicalInspectionValuation representation = refl

canonicalThreeSixInspectionValue :
  proj₁
    (Rep.inspectRepresentation
      canonicalHalfFrameScaleValuation
      chartedThreeSix)
  ≡ Rep.threeSix
canonicalThreeSixInspectionValue = refl

canonicalFiftyPercentInspectionValue :
  proj₁
    (Rep.inspectRepresentation
      canonicalHalfFrameScaleValuation
      chartedFiftyPercent)
  ≡ Rep.fiftyHundredths
canonicalFiftyPercentInspectionValue = refl
