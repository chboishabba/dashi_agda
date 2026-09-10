module DASHI.Wikimedia.IbrahimColourMetamerismProjectionFibreSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ProjectionFibre as Fibre
import DASHI.Core.ProjectionCategory as PC
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Wikimedia.Ibrahim36927PantsColourTextileSweetgrassSnowballExact as Cross
import DASHI.Visual.ColourPerceptionDASHI as Colour
import DASHI.Visual.ColourPerceptionCrossPollination as ColourX
import DASHI.Physics.Closure.LightTransportFibreClosure as Light

------------------------------------------------------------------------
-- COLOUR METAMERISM AS A PROJECTION-FIBRE / FACTORISATION REGRESSION
--
-- CIE source coordinates:
--   ISO/CIE 11664-1:2019, 10.25039/DS11664-1.2019
--   CIE 015:2018,       10.25039/TR.015.2018
--   CIE 080-1989, special metamerism index: change in observer
--
-- Source claim shape:
--   distinct spectral radiance/power distributions may produce identical
--   tristimulus values for a declared illuminant and observer.  Changing the
--   illuminant or observer may break the match.
--
-- This file does not fabricate measured spectra or a numerical CIE observer.
-- It records the exact logical shape needed for later data-backed witnesses.
------------------------------------------------------------------------

record MetamericPairSurface : Set where
  constructor metameric-pair-surface
  field
    leftSpectrumReference : String
    rightSpectrumReference : String
    declaredObserverReference : String
    declaredIlluminantReference : String
    sameTristimulusUnderDeclaredConditions : Bool
    spectraKnownDistinct : Bool
    measuredNumericalWitnessPaid : Bool
open MetamericPairSurface public

sourceShapeMetamerPair : MetamericPairSurface
sourceShapeMetamerPair = metameric-pair-surface
  "spectral distribution s1"
  "spectral distribution s2"
  "CIE standard colorimetric observer / declared observer"
  "declared illuminant"
  true true false

record MetamerismSourceCoordinate : Set where
  constructor metamerism-source-coordinate
  field
    title : String
    identifier : String
    role : String
    theoremWitnessCreated : Bool
open MetamerismSourceCoordinate public

cieObserverStandard : MetamerismSourceCoordinate
cieObserverStandard = metamerism-source-coordinate
  "ISO/CIE 11664-1:2019 Colorimetry Part 1: CIE standard colorimetric observers"
  "10.25039/DS11664-1.2019"
  "specifies colour-matching functions for standard colorimetric observers"
  false

cieColorimetryReport : MetamerismSourceCoordinate
cieColorimetryReport = metamerism-source-coordinate
  "CIE 015:2018 Colorimetry, 4th Edition"
  "10.25039/TR.015.2018"
  "colorimetric observer/illuminant/tristimulus practice and formula source"
  false

cieObserverMetamerism : MetamerismSourceCoordinate
cieObserverMetamerism = metamerism-source-coordinate
  "CIE 080-1989 Special metamerism index: Change in observer"
  "CIE 080-1989"
  "explicit source for equal tristimulus with different spectral radiance factors and observer-dependent mismatch"
  false

------------------------------------------------------------------------
-- Projection reading.
------------------------------------------------------------------------

data SpectralState : Set where
  spectrumA : SpectralState
  spectrumB : SpectralState

data TristimulusSurface : Set where
  sameXYZ : TristimulusSurface

observeTristimulus : SpectralState → TristimulusSurface
observeTristimulus spectrumA = sameXYZ
observeTristimulus spectrumB = sameXYZ

spectraDistinct : ¬ (spectrumA ≡ spectrumB)
spectraDistinct ()

metamersShareObservedCoordinate :
  observeTristimulus spectrumA ≡ observeTristimulus spectrumB
metamersShareObservedCoordinate = refl

------------------------------------------------------------------------
-- This is the exact finite witness shape ProjectionFibre is intended to
-- represent: multiple carrier states collapse to one observable.  The local
-- two-point example is a logical regression, not a claim that it numerically
-- instantiates CIE colour matching functions.
------------------------------------------------------------------------

record MetamerProjectionBoundary : Set where
  constructor metamer-projection-boundary
  field
    distinctCarrierStatesMayShareObservation : Bool
    colourMatchQueryMayUseObservedCoordinate : Bool
    exactSpectrumIdentityFactorsThroughTristimulus : Bool
    observerIdentityMayMatter : Bool
    illuminantIdentityMayMatter : Bool
    observerOrIlluminantRevisionMayReopenComparison : Bool
    tristimulusEqualityCreatesQualiaIdentity : Bool
    sourceClaimCreatesMeasuredWitness : Bool
    failedSpectrumFactorisationSnowballsSpectralAxis : Bool
open MetamerProjectionBoundary public

canonicalMetamerProjectionBoundary : MetamerProjectionBoundary
canonicalMetamerProjectionBoundary = metamer-projection-boundary
  true true false true true true false false true

------------------------------------------------------------------------
-- WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data SameTristimulusMeansSameSpectrum : Set where
data SameTristimulusMeansSameQuale : Set where
data StandardObserverMeansEveryHumanObserver : Set where
data SameColourUnderOneIlluminantMeansSameUnderEveryIlluminant : Set where
data CIESourceCreatesLocalNumericalWitness : Set where

tristimulusDoesNotRecoverSpectrum : SameTristimulusMeansSameSpectrum → ⊥
tristimulusDoesNotRecoverSpectrum ()

tristimulusDoesNotRecoverQuale : SameTristimulusMeansSameQuale → ⊥
tristimulusDoesNotRecoverQuale ()

standardObserverIsNotEveryObserver : StandardObserverMeansEveryHumanObserver → ⊥
standardObserverIsNotEveryObserver ()

oneIlluminantDoesNotUniversaliseMatch :
  SameColourUnderOneIlluminantMeansSameUnderEveryIlluminant → ⊥
oneIlluminantDoesNotUniversaliseMatch ()

sourceDoesNotCreateMeasuredWitness : CIESourceCreatesLocalNumericalWitness → ⊥
sourceDoesNotCreateMeasuredWitness ()

------------------------------------------------------------------------
-- Existing repo owners retained.
------------------------------------------------------------------------

projectionFibreOwner : Fibre.ProjectionFibre PC.canonicalProjectionCategory
projectionFibreOwner = Fibre.canonicalProjectionFibre

colourBoundary : Colour.ColourPerceptionBoundary
colourBoundary = Colour.canonicalColourPerceptionBoundary

colourCrossPollination : ColourX.ColourCrossPollinationCertificate
colourCrossPollination = ColourX.canonicalColourCrossPollinationCertificate

crossDomainBoundary : Cross.Ibrahim369ColourTextileBoundary
crossDomainBoundary = Cross.canonicalIbrahim369ColourTextileBoundary

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary

------------------------------------------------------------------------
-- Light-transport linkage remains typed: the spectral state feeding an
-- observer arises downstream of geometry/material/illumination/visibility.
-- A metameric observer collision does not erase those transport coordinates.
------------------------------------------------------------------------

record LightMetamerismBidiBoundary : Set where
  constructor light-metamerism-bidi-boundary
  field
    materialSpectrumAffectsColourObservation : Bool
    illuminationAffectsMetamericMatch : Bool
    observerAffectsMetamericMatch : Bool
    sameColourCoordinateRecoversMaterialFibre : Bool
    sameColourCoordinateRecoversLightTransportHistory : Bool
    hiddenTransportAxesRemainSnowballCandidates : Bool
open LightMetamerismBidiBoundary public

canonicalLightMetamerismBidiBoundary : LightMetamerismBidiBoundary
canonicalLightMetamerismBidiBoundary = light-metamerism-bidi-boundary
  true true true false false true
