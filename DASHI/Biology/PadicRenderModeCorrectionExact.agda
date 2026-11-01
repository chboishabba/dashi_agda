module DASHI.Biology.PadicRenderModeCorrectionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.RenderablePadicReasoningFieldExact as Legacy
import DASHI.Visualisation.RendererStabilityExact as Exact

------------------------------------------------------------------------
-- The earlier finite `renderTwoSamples` table was useful only to distinguish
-- rendering modes.  Its straight-alpha branch was not the compositing law.
-- This correction makes that authority boundary executable and points the
-- promoted theorem surface to the exact fraction-valued recurrence.

legacyStraightAlphaCode : Nat
legacyStraightAlphaCode =
  Legacy.renderTwoSamples Legacy.straightAlphaCompositing 3 4

legacyStraightAlphaCodeIsSix : legacyStraightAlphaCode ≡ 6
legacyStraightAlphaCodeIsSix = refl

exactStraightAlphaNumerator : Nat
exactStraightAlphaNumerator =
  Exact.numerator
    (Exact.frontToBackAlpha Exact.half Exact.threeQuarters)

exactStraightAlphaDenominator : Nat
exactStraightAlphaDenominator =
  Exact.denominator
    (Exact.frontToBackAlpha Exact.half Exact.threeQuarters)

exactStraightAlphaIsFourteenSixteenths :
  exactStraightAlphaNumerator ≡ 14
  ×
  exactStraightAlphaDenominator ≡ 16
exactStraightAlphaIsFourteenSixteenths = refl , refl

legacyCodeIsNotExactAlphaNumerator :
  legacyStraightAlphaCode ≡ exactStraightAlphaNumerator → ⊥
legacyCodeIsNotExactAlphaNumerator ()

record PadicRenderModeCorrectionBoundary : Set where
  constructor padicRenderModeCorrectionBoundary
  field
    legacyTwoSampleTableIsExactStraightAlphaCompositing : Bool
    legacyTwoSampleTableIsExactStraightAlphaCompositingIsFalse :
      legacyTwoSampleTableIsExactStraightAlphaCompositing ≡ false

    exactFractionRecurrenceIsPromotedCompositingSurface : Bool
    exactFractionRecurrenceIsPromotedCompositingSurfaceIsTrue :
      exactFractionRecurrenceIsPromotedCompositingSurface ≡ true

open PadicRenderModeCorrectionBoundary public

canonicalPadicRenderModeCorrectionBoundary :
  PadicRenderModeCorrectionBoundary
canonicalPadicRenderModeCorrectionBoundary =
  padicRenderModeCorrectionBoundary false refl true refl
