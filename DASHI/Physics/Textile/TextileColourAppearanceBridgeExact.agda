module DASHI.Physics.Textile.TextileColourAppearanceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Observer/display projection above physical radiance.
--
-- The repository's optical kernel already records the standard boundary:
-- spectral radiance -> observer tristimulus coordinates -> display RGB.
-- This module instantiates that boundary for the same textile radiance sample
-- without identifying the displayed colour with the physical spectrum.
------------------------------------------------------------------------

record ColourProjection
    (Radiance Tristimulus DisplaySample : Set)
    (radiance : Radiance) : Set₁ where
  constructor colour-projection
  field
    standardObserverConvention : String
    illuminantAndAdaptationConvention : String
    displayTransferAndGamut : String

    toTristimulus : Radiance → Tristimulus
    toDisplay : Tristimulus → DisplaySample

    tristimulus : Tristimulus
    displayedSample : DisplaySample

    tristimulusLaw : tristimulus ≡ toTristimulus radiance
    displayLaw : displayedSample ≡ toDisplay tristimulus

open ColourProjection public

record TextileColourObservation
    {OpticalState Illumination OpticalObserver Radiance Tristimulus DisplaySample : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (state : OpticalState)
    (observer : OpticalObserver) : Set₁ where
  constructor textile-colour-observation
  field
    radianceObservation : Optical.TextileRadianceObservation model state observer
    projection :
      ColourProjection
        Radiance
        Tristimulus
        DisplaySample
        (Optical.radianceSample radianceObservation)

open TextileColourObservation public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data DisplayedColourIsPhysicalSpectrum : Set where

displayedColourIsNotPhysicalSpectrum :
  DisplayedColourIsPhysicalSpectrum → ⊥
displayedColourIsNotPhysicalSpectrum ()

data SameDisplayedColourImpliesSameTextileRadiance : Set where

sameDisplayedColourDoesNotImplySameTextileRadiance :
  SameDisplayedColourImpliesSameTextileRadiance → ⊥
sameDisplayedColourDoesNotImplySameTextileRadiance ()

data SameColourImpliesSameLustre : Set where

sameColourDoesNotImplySameLustre :
  SameColourImpliesSameLustre → ⊥
sameColourDoesNotImplySameLustre ()
