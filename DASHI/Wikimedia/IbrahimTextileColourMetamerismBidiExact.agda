module DASHI.Wikimedia.IbrahimTextileColourMetamerismBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimColourMetamerismProjectionFibreSnowballExact as Metamer
import DASHI.Wikimedia.IbrahimProjectionCollisionColourTextilePantsBidiExact as Collision
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Physics.Textile.TextileColourAppearanceBridgeExact as TextileColour

------------------------------------------------------------------------
-- TEXTILE COLOUR <-> CIE METAMERISM BIDI WELD
--
-- Repo-native owner:
--   textile spectral radiance -> tristimulus -> displayed sample,
--   with observer, illuminant/adaptation and display conventions retained.
--
-- External source-side metamerism:
--   different spectra can produce the same tristimulus match under declared
--   observer/illuminant conditions.
--
-- The weld is a shared projection-loss shape.  It does not identify CIE's
-- empirical/standardized colour-matching functions with any toy DASHI colour
-- carrier and does not fabricate textile measurements.
------------------------------------------------------------------------

record TextileMetamerismWeld : Set where
  constructor textile-metamerism-weld
  field
    repoRadianceToTristimulusProjectionExists : Bool
    repoTristimulusToDisplayProjectionExists : Bool
    repoAlreadyBlocksDisplayToRadianceInverse : Bool
    cieMetamerismSuppliesExternalProjectionCollisionPattern : Bool
    sameDisplayedColourMayHideDifferentRadiance : Bool
    sameTristimulusMayHideDifferentSpectrum : Bool
    observerConventionMustBeRetained : Bool
    illuminantConventionMustBeRetained : Bool
    displayConventionMustBeRetained : Bool
    sameDisplayedColourDeterminesWeaveTopology : Bool
    sameDisplayedColourDeterminesMaterialFibre : Bool
    externalMetamerismCreatesMeasuredTextileWitness : Bool
open TextileMetamerismWeld public

canonicalTextileMetamerismWeld : TextileMetamerismWeld
canonicalTextileMetamerismWeld = textile-metamerism-weld
  true true true true true true true true true false false false

------------------------------------------------------------------------
-- Exact repo non-promotion theorem is re-exported as the local half of the
-- BIDI weld.  No new proof of optics is introduced here.
------------------------------------------------------------------------

sameDisplayedColourStillDoesNotDetermineRadiance :
  TextileColour.SameDisplayedColourImpliesSameTextileRadiance → ⊥
sameDisplayedColourStillDoesNotDetermineRadiance =
  TextileColour.sameDisplayedColourDoesNotImplySameTextileRadiance

------------------------------------------------------------------------
-- Consumer-indexed snowball consequences.
------------------------------------------------------------------------

data TextileColourQuery : Set where
  displayedColourQuery : TextileColourQuery
  tristimulusQuery : TextileColourQuery
  exactRadianceQuery : TextileColourQuery
  materialIdentityQuery : TextileColourQuery
  weaveTopologyQuery : TextileColourQuery
  lustreQuery : TextileColourQuery

record TextileColourFactorisationStatus : Set where
  constructor textile-colour-factorisation-status
  field
    query : TextileColourQuery
    displayedCoordinateMaySuffice : Bool
    hiddenOpticalOrStructuralAxisRequired : Bool
    failedFactorisationMaySnowballAxis : Bool
open TextileColourFactorisationStatus public

displayedColourStatus : TextileColourFactorisationStatus
displayedColourStatus = textile-colour-factorisation-status displayedColourQuery true false false

tristimulusStatus : TextileColourFactorisationStatus
tristimulusStatus = textile-colour-factorisation-status tristimulusQuery true false false

exactRadianceStatus : TextileColourFactorisationStatus
exactRadianceStatus = textile-colour-factorisation-status exactRadianceQuery false true true

materialIdentityStatus : TextileColourFactorisationStatus
materialIdentityStatus = textile-colour-factorisation-status materialIdentityQuery false true true

weaveTopologyStatus : TextileColourFactorisationStatus
weaveTopologyStatus = textile-colour-factorisation-status weaveTopologyQuery false true true

lustreStatus : TextileColourFactorisationStatus
lustreStatus = textile-colour-factorisation-status lustreQuery false true true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CIETristimulusEqualsDASHIMCCP : Set where
data MetamerismDeterminesWeave : Set where
data SameRGBMeansSameMaterial : Set where
data ObserverConventionMayBeDropped : Set where
data IlluminantMayBeDropped : Set where

cieTristimulusIsNotMCCPIdentity : CIETristimulusEqualsDASHIMCCP → ⊥
cieTristimulusIsNotMCCPIdentity ()

metamerismDoesNotDetermineWeave : MetamerismDeterminesWeave → ⊥
metamerismDoesNotDetermineWeave ()

sameRGBDoesNotDetermineMaterial : SameRGBMeansSameMaterial → ⊥
sameRGBDoesNotDetermineMaterial ()

observerMustRemainIndexed : ObserverConventionMayBeDropped → ⊥
observerMustRemainIndexed ()

illuminantMustRemainIndexed : IlluminantMayBeDropped → ⊥
illuminantMustRemainIndexed ()

metamerBoundary : Metamer.MetamerProjectionBoundary
metamerBoundary = Metamer.canonicalMetamerProjectionBoundary

collisionBoundary : Collision.ProjectionCollisionBoundary
collisionBoundary = Collision.canonicalProjectionCollisionBoundary

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
