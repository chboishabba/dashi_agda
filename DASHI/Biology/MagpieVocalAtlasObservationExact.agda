module DASHI.Biology.MagpieVocalAtlasObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BioacousticYouTubeSeedSourceExact as Seed

------------------------------------------------------------------------
-- MAGPIE VOCAL ATLAS: APPEND-ONLY SITUATED OBSERVATIONS
--
-- This owner records what was observed and how precisely its identity/location
-- are paid.  It does not decode semantics, infer dialect, or upgrade a source
-- title into biological identity.
------------------------------------------------------------------------

data VocalObservationLevel : Set where
  segment : VocalObservationLevel
  call : VocalObservationLevel
  callSequence : VocalObservationLevel
  bout : VocalObservationLevel
  interactionEpisode : VocalObservationLevel
  groupRepertoire : VocalObservationLevel
  regionalRepertoire : VocalObservationLevel
  speciesWideAtlas : VocalObservationLevel

data LocationPrecision : Set where
  locationUnknown : LocationPrecision
  countryLevel : LocationPrecision
  regionLevel : LocationPrecision
  cityLevel : LocationPrecision
  siteLevel : LocationPrecision
  approximateCoordinates : LocationPrecision
  exactCoordinates : LocationPrecision

data IdentityStatus : Set where
  identityUnknown : IdentityStatus
  identityCandidate : IdentityStatus
  identitySourceBound : IdentityStatus
  identityExternallyPaid : IdentityStatus

data ObservationDecision : Set where
  candidate : ObservationDecision
  promoted : ObservationDecision
  abstain : ObservationDecision
  rejected : ObservationDecision

record MagpieVocalEvent : Set where
  constructor magpie-vocal-event
  field
    observationLevel : VocalObservationLevel
    eventId : String
    sourceId : String
    mediaId : String
    startTimeReference : String
    endTimeReference : String
    sourceClockReference : String
    sourceProvenance : String
    mediaByteIdentity : String
    acquisitionMethod : String

    speciesIdentityStatus : IdentityStatus
    individualIdentityStatus : IdentityStatus
    groupIdentityStatus : IdentityStatus

    locationValue : String
    locationPrecision : LocationPrecision
    locationProvenance : String
    regionPopulationLabel : String
    physicalTimeContext : String
    habitatEnvironmentContext : String
    observedSurrounds : String
    behaviourSocialContext : String

    acousticObservationReference : String
    visibleMotorObservationReference : String
    candidateCallFamily : String
    candidateFunctionalContext : String
    candidateSemanticFamily : String

    decision : ObservationDecision
    confidenceResidualReference : String
    receiptReferences : List String
    parentObservationReferences : List String
    reopeningDependencyReferences : List String

open MagpieVocalEvent public

------------------------------------------------------------------------
-- Initial acquisition observations.  These pay only the source/video-id layer.
------------------------------------------------------------------------

magpieChatterSeedObservation : MagpieVocalEvent
magpieChatterSeedObservation = magpie-vocal-event
  interactionEpisode
  "youtube:Kz4SvP0c_VE:whole-source-candidate"
  "youtube:Kz4SvP0c_VE"
  (Seed.videoId Seed.magpieChatterSeed)
  "unsegmented source start; runtime PTS unpaid"
  "unsegmented source end; runtime PTS unpaid"
  "Animalexic FrameStreamer source-relative pts_time when acquired"
  "BioacousticYouTubeSeedSourceExact.magpieChatterSeed"
  "unpaid: transient YouTube representation is not stable media-byte identity"
  "Animalexic yt-dlp transient resolution + ffmpeg stream"
  identityCandidate identityUnknown identityUnknown
  "unresolved"
  locationUnknown
  "no exact location receipt retained in current seed owner"
  "unresolved"
  "unresolved"
  "unresolved"
  "external source role: magpie chatter; behavioural interpretation remains bounded"
  "pending synchronized audio feature extraction"
  "pending visible-motion extraction"
  "unassigned"
  "unassigned"
  "unassigned"
  candidate
  "unpaid"
  ("BioacousticYouTubeSeedSourceExact" ∷ [])
  []
  ("runtime metadata" ∷ "event segmentation" ∷ "species/group/location refinement" ∷ [])

unresolvedSeedObservation : MagpieVocalEvent
unresolvedSeedObservation = magpie-vocal-event
  interactionEpisode
  "youtube:8u_7lFB5iLg:whole-source-candidate"
  "youtube:8u_7lFB5iLg"
  (Seed.videoId Seed.unresolvedSeed)
  "unsegmented source start; runtime PTS unpaid"
  "unsegmented source end; runtime PTS unpaid"
  "Animalexic FrameStreamer source-relative pts_time when acquired"
  "BioacousticYouTubeSeedSourceExact.unresolvedSeed"
  "unpaid: transient YouTube representation is not stable media-byte identity"
  "Animalexic yt-dlp transient resolution + ffmpeg stream"
  identityUnknown identityUnknown identityUnknown
  "unresolved"
  locationUnknown
  "no location receipt retained"
  "unresolved"
  "unresolved"
  "unresolved"
  "unresolved"
  "pending synchronized audio feature extraction"
  "pending visible-motion extraction"
  "unassigned"
  "unassigned"
  "unassigned"
  candidate
  "unpaid"
  ("BioacousticYouTubeSeedSourceExact" ∷ [])
  []
  ("runtime metadata" ∷ "species identity" ∷ "event segmentation" ∷ "location/context" ∷ [])

magpieSingingSeedObservation : MagpieVocalEvent
magpieSingingSeedObservation = magpie-vocal-event
  interactionEpisode
  "youtube:oYEYc8Ge3nw:whole-source-candidate"
  "youtube:oYEYc8Ge3nw"
  (Seed.videoId Seed.magpieSingingSeed)
  "unsegmented source start; runtime PTS unpaid"
  "unsegmented source end; runtime PTS unpaid"
  "Animalexic FrameStreamer source-relative pts_time when acquired"
  "BioacousticYouTubeSeedSourceExact.magpieSingingSeed"
  "unpaid: transient YouTube representation is not stable media-byte identity"
  "Animalexic yt-dlp transient resolution + ffmpeg stream"
  identityCandidate identityUnknown identityUnknown
  "unresolved"
  locationUnknown
  "WA Department of Education is a source-context receipt only; it does not locate the recording"
  "unresolved"
  "unresolved"
  "unresolved"
  "external source role: Australian magpie singing; exact behaviour/individual/location unpaid"
  "pending synchronized audio feature extraction"
  "pending visible-motion extraction"
  "unassigned"
  "unassigned"
  "unassigned"
  candidate
  "unpaid"
  ("BioacousticYouTubeSeedSourceExact" ∷ [])
  []
  ("runtime metadata" ∷ "event segmentation" ∷ "individual/group identity" ∷ "location precision" ∷ [])

initialAtlasObservations : List MagpieVocalEvent
initialAtlasObservations =
  magpieChatterSeedObservation ∷
  unresolvedSeedObservation ∷
  magpieSingingSeedObservation ∷ []

record MagpieVocalObservationBoundary : Set where
  constructor magpie-vocal-observation-boundary
  field
    sourceTitleDoesNotCreateExactLocation : Bool
    videoSpeciesLabelDoesNotCreateIndividualIdentity : Bool
    rawAmplitudeDoesNotCreateCalibratedSPL : Bool
    visibleMotionDoesNotCreateBiomechanicalWork : Bool
    avSynchronyDoesNotCreateCausality : Bool
    unknownIdentityRemainsFirstClass : Bool
    higherLevelObjectRetainsLowerObservationIdentity : Bool
    appendOnlyObservationHistory : Bool
    laterRefinementMayReopenDependencies : Bool

open MagpieVocalObservationBoundary public

canonicalMagpieVocalObservationBoundary : MagpieVocalObservationBoundary
canonicalMagpieVocalObservationBoundary =
  magpie-vocal-observation-boundary
    true true true true true true true true true

observationReading : String
observationReading =
  "A magpie vocal atlas begins with append-only situated observations, not decoded words. Source/media identity, time, biological identity, location precision, acoustic form, visible motor state, behaviour/context and provenance remain separate. Unknown coordinates stay explicit and later evidence may refine or reopen them without erasing the earlier candidate state."
