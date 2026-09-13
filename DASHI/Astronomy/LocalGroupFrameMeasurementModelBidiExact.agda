module DASHI.Astronomy.LocalGroupFrameMeasurementModelBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BIDI separation for the Local Group observational/model frame.
------------------------------------------------------------------------

data FrameLayer : Set where
  measuredLayer : FrameLayer
  tabulatedLayer : FrameLayer
  derivedFrameLayer : FrameLayer
  modelLayer : FrameLayer
  renderingLayer : FrameLayer

record FrameDatum : Set where
  constructor frameDatum
  field
    identity : String
    layer : FrameLayer
    coordinateDescription : String
    sourceDescription : String

open FrameDatum public

sunDatum : FrameDatum
sunDatum = frameDatum
  "Sun"
  derivedFrameLayer
  "reference-state coordinate in the adopted Galactocentric/model frame"
  "frame construction; not a directly observed Cartesian Local Group coordinate"

galacticCentreDatum : FrameDatum
galacticCentreDatum = frameDatum
  "Galactic centre"
  derivedFrameLayer
  "origin/reference coordinate of adopted Galactocentric frame"
  "frame convention"

m31Datum : FrameDatum
m31Datum = frameDatum
  "M31"
  derivedFrameLayer
  "position derived from source observables and adopted frame transforms"
  "source-bound Local Group reconstruction"

m33Datum : FrameDatum
m33Datum = frameDatum
  "M33"
  derivedFrameLayer
  "position derived from source observables and adopted frame transforms"
  "source-bound Local Group reconstruction"

localGroupBarycentreDatum : FrameDatum
localGroupBarycentreDatum = frameDatum
  "Local Group barycentre"
  modelLayer
  "model-derived barycentric coordinate"
  "model construction; not a directly measured physical marker"

renderedPointImpliesDirectMeasurement : FrameDatum → Bool
renderedPointImpliesDirectMeasurement _ = false

renderedPointImpliesDirectMeasurementIsFalse :
  (d : FrameDatum) → renderedPointImpliesDirectMeasurement d ≡ false
renderedPointImpliesDirectMeasurementIsFalse d = refl

modelBarycentreImpliesMeasuredBarycentre : Bool
modelBarycentreImpliesMeasuredBarycentre = false

modelBarycentreImpliesMeasuredBarycentreIsFalse :
  modelBarycentreImpliesMeasuredBarycentre ≡ false
modelBarycentreImpliesMeasuredBarycentreIsFalse = refl

sameRenderedCoordinateImpliesSameProvenance : Bool
sameRenderedCoordinateImpliesSameProvenance = false

sameRenderedCoordinateImpliesSameProvenanceIsFalse :
  sameRenderedCoordinateImpliesSameProvenance ≡ false
sameRenderedCoordinateImpliesSameProvenanceIsFalse = refl
