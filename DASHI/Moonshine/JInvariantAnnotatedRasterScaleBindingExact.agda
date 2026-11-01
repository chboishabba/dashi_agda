module DASHI.Moonshine.JInvariantAnnotatedRasterScaleBindingExact where

------------------------------------------------------------------------
-- USER-ANNOTATED RASTER -> EXACT SEAM-SCALE SOURCE BINDING
--
-- Conversation raster:
--   dimensions 1920 x 1336
--   sha256 1f4ee58e1326e598e7b04d14e93e9f279f8f1f454c58e1d84afdec2c572538f5
--
-- Pixel centres below were measured on that raster around the eight labelled
-- dark order-three centres.  The exact scale is then the already-proved
-- D_k=k^2+k+1 value of the bound candidate index.
--
-- IMPORTANT: this is an empirical/source binding receipt.  It does not turn
-- raster darkness into an analytic Mobius theorem and does not replace the
-- interval-valued analytic containment layer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale
import DASHI.Moonshine.JInvariantOrderThreeVisibleScaleUniquenessBidiExact as Visible

rasterSha256 : String
rasterSha256 =
  "1f4ee58e1326e598e7b04d14e93e9f279f8f1f454c58e1d84afdec2c572538f5"

rasterWidth : Nat
rasterWidth = 1920

rasterHeight : Nat
rasterHeight = 1336

record PixelCentre : Set where
  constructor pixel-centre
  field
    xPixel : Nat
    yPixel : Nat

open PixelCentre public

measuredCentre : Visible.VisibleEightIndex → PixelCentre
measuredCentre Visible.visible0 = pixel-centre 758 708
measuredCentre Visible.visible1 = pixel-centre 756 1082
measuredCentre Visible.visible2 = pixel-centre 849 1194
measuredCentre Visible.visible3 = pixel-centre 908 1233
measuredCentre Visible.visible4 = pixel-centre 945 1252
measuredCentre Visible.visible5 = pixel-centre 969 1261
measuredCentre Visible.visible6 = pixel-centre 987 1266
measuredCentre Visible.visible7 = pixel-centre 1000 1269

-- Radius retained as measurement uncertainty around the local dark-centre pick.
pixelRadius : Nat
pixelRadius = 8

boundIndex : Visible.VisibleEightIndex → Nat
boundIndex = Visible.visibleIndex

boundExactScale : Visible.VisibleEightIndex → Nat
boundExactScale i = Scale.seamScale (boundIndex i)

bound0Scale : boundExactScale Visible.visible0 ≡ 1
bound0Scale = refl

bound1Scale : boundExactScale Visible.visible1 ≡ 3
bound1Scale = refl

bound2Scale : boundExactScale Visible.visible2 ≡ 7
bound2Scale = refl

bound3Scale : boundExactScale Visible.visible3 ≡ 13
bound3Scale = refl

bound4Scale : boundExactScale Visible.visible4 ≡ 21
bound4Scale = refl

bound5Scale : boundExactScale Visible.visible5 ≡ 31
bound5Scale = refl

bound6Scale : boundExactScale Visible.visible6 ≡ 43
bound6Scale = refl

bound7Scale : boundExactScale Visible.visible7 ≡ 57
bound7Scale = refl

record AnnotatedRasterScaleReceipt
  (candidate : Visible.VisibleEightIndex) : Set where
  constructor annotated-raster-scale-receipt
  field
    centre : PixelCentre
    centreIsMeasured : centre ≡ measuredCentre candidate
    uncertaintyRadiusPixels : Nat
    uncertaintyRadiusIsEight : uncertaintyRadiusPixels ≡ pixelRadius
    exactScale : Nat
    exactScaleIsCandidateScale : exactScale ≡ boundExactScale candidate

open AnnotatedRasterScaleReceipt public

canonicalRasterScaleReceipt :
  (candidate : Visible.VisibleEightIndex) →
  AnnotatedRasterScaleReceipt candidate
canonicalRasterScaleReceipt candidate =
  annotated-raster-scale-receipt
    (measuredCentre candidate)
    refl
    pixelRadius
    refl
    (boundExactScale candidate)
    refl

record AnnotatedRasterBindingBoundary : Set where
  constructor annotated-raster-binding-boundary
  field
    actualConversationRasterDigestRetained : Bool
    pixelCentresMeasured : Bool
    pixelUncertaintyRetained : Bool
    candidateToExactScaleCompilerOwned : Bool
    userAnnotationUsedAsEmpiricalBinding : Bool
    rasterBindingAloneProvesAnalyticMobiusContainment : Bool
    rasterBindingAloneProvesFullJFineState : Bool

canonicalAnnotatedRasterBindingBoundary : AnnotatedRasterBindingBoundary
canonicalAnnotatedRasterBindingBoundary =
  annotated-raster-binding-boundary
    true true true true true false false
