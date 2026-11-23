module DASHI.Moonshine.JInvariantFormulaic369ReproductionBundleExact where

------------------------------------------------------------------------
-- FORMULAIC REPRODUCTION BUNDLE
--
-- Once concrete analytic and raster producers are supplied, this bundle has an
-- executable surface Pixel -> Colour.  Its semantics are already fixed by the
-- formulaic j renderer and modular replication owners.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369ModularReplicationExact as Replicate

record J369ReproductionBundle : Set₁ where
  constructor j369-reproduction-bundle
  field
    renderer : Render.JPhaseRenderingAlgebra
    raster : Render.J369RasterProducer renderer
    modular : Replicate.J369ModularAction renderer

open J369ReproductionBundle public

Pixel : J369ReproductionBundle → Set
Pixel B = Render.Pixel (raster B)

Colour : (B : J369ReproductionBundle) → Set
Colour B = Render.Colour (renderer B)

sample :
  (B : J369ReproductionBundle) →
  Pixel B →
  Render.J369RenderSample (renderer B)
sample B px = Render.renderPixel (renderer B) (raster B) px

pixelColour :
  (B : J369ReproductionBundle) →
  Pixel B →
  Colour B
pixelColour B px = Render.renderedColour (sample B px)

pixelPhase :
  (B : J369ReproductionBundle) →
  (px : Pixel B) →
  Render.Phase (renderer B)
pixelPhase B px = Render.exactPhase (sample B px)

pixelObserver3 :
  (B : J369ReproductionBundle) →
  (px : Pixel B) →
  DASHI.Biology.TriadicKernelLiftQuotientExact.KernelTrit
pixelObserver3 B px = Render.observer3 (sample B px)

------------------------------------------------------------------------
-- The semantic render path cannot bypass the formulaic sample.
------------------------------------------------------------------------

pixelColourIsFormulaic :
  (B : J369ReproductionBundle) →
  (px : Pixel B) →
  pixelColour B px ≡
  Render.jColour
    (renderer B)
    (Render.pointAt (raster B) px)
pixelColourIsFormulaic B px = refl

pixelPhaseIsFormulaic :
  (B : J369ReproductionBundle) →
  (px : Pixel B) →
  pixelPhase B px ≡
  Render.jPhase
    (renderer B)
    (Render.pointAt (raster B) px)
pixelPhaseIsFormulaic B px = refl

------------------------------------------------------------------------
-- Reproduction status.
------------------------------------------------------------------------

record ReproductionBundleFrontier : Set where
  constructor reproduction-bundle-frontier
  field
    pixelToColourSurfaceOwned : Bool
    pixelToContinuousPhaseSurfaceOwned : Bool
    phaseRetainedBefore369Observation : Bool
    modularReplicationCompilerOwned : Bool
    concreteComplexJImplementationRequired : Bool
    concreteRasterSerializationRequired : Bool

canonicalReproductionBundleFrontier : ReproductionBundleFrontier
canonicalReproductionBundleFrontier =
  reproduction-bundle-frontier true true true true true true
