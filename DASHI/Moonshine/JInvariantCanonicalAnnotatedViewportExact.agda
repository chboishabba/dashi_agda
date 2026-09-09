module DASHI.Moonshine.JInvariantCanonicalAnnotatedViewportExact where

------------------------------------------------------------------------
-- CANONICAL VIEWPORT FOR THE ANNOTATED j-PHASE IMAGE USED BY THIS TRANCHE
--
-- This is a source/measurement receipt for the plotted coordinate frame that
-- has actually been inspected in the BIDI loop.  It is deliberately separate
-- from any claim about the exact Jan Homann Mathematica notebook viewport.
--
--   x in [-3/2, 6/5]   = [-1.5, 1.2]
--   y in [0, 39/20]    = [0, 1.95]
--
-- The runtime renderer may use these values as its canonical DASHI regression
-- viewport.  "Canonical for our regression" != "historical source notebook
-- viewport recovered".
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data SignedRationalEndpoint : Set where
  negative : Nat → Nat → SignedRationalEndpoint
  nonnegative : Nat → Nat → SignedRationalEndpoint

record RationalViewport : Set where
  constructor rational-viewport
  field
    xMin xMax yMin yMax : SignedRationalEndpoint

open RationalViewport public

canonicalAnnotatedViewport : RationalViewport
canonicalAnnotatedViewport =
  rational-viewport
    (negative 3 2)
    (nonnegative 6 5)
    (nonnegative 0 1)
    (nonnegative 39 20)

canonicalWidthPixels : Nat
canonicalWidthPixels = 947

canonicalHeightPixels : Nat
canonicalHeightPixels = 704

viewportPurpose : String
viewportPurpose =
  "canonical DASHI regression viewport from the inspected full-axis j image; not a recovered Mathematica notebook viewport"

record ViewportAuthorityBoundary : Set where
  constructor viewport-authority-boundary
  field
    annotatedAxesObserved : Bool
    exactRationalEndpointsRecorded : Bool
    suitableForDASHIRegression : Bool
    provesHistoricalHomannNotebookViewport : Bool
    provesAnalyticPixelCalibration : Bool

canonicalViewportAuthorityBoundary : ViewportAuthorityBoundary
canonicalViewportAuthorityBoundary =
  viewport-authority-boundary true true true false false

historicalViewportNotPromoted :
  ViewportAuthorityBoundary.provesHistoricalHomannNotebookViewport
    canonicalViewportAuthorityBoundary ≡ false
historicalViewportNotPromoted = refl

analyticPixelCalibrationNotPromoted :
  ViewportAuthorityBoundary.provesAnalyticPixelCalibration
    canonicalViewportAuthorityBoundary ≡ false
analyticPixelCalibrationNotPromoted = refl
