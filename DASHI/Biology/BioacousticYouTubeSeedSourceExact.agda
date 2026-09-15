module DASHI.Biology.BioacousticYouTubeSeedSourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- YOUTUBE BIRDSONG SEED SOURCES
--
-- Source-bound acquisition candidates for the first audiovisual birdsong
-- experiments.  Animalexic owns transient runtime acquisition through its
-- existing FrameStreamer (yt-dlp metadata/stream resolution + ffmpeg decode).
-- A YouTube URL/video id pays a locator identity, not byte identity, species
-- identity, calibrated acoustics, physiology, energetics, or causal mechanism.
------------------------------------------------------------------------

record YouTubeSeedSource : Set where
  constructor youtube-seed-source
  field
    videoId : String
    sourceURL : String
    sourceRole : String
    externalLabel : String
    labelBasis : String
    metadataResolutionStatus : String

open YouTubeSeedSource public

magpieChatterSeed : YouTubeSeedSource
magpieChatterSeed = youtube-seed-source
  "Kz4SvP0c_VE"
  "https://www.youtube.com/watch?v=Kz4SvP0c_VE"
  "candidate audiovisual source for chatter/song-versus-visible-motion analysis"
  "magpie chatter"
  "external contextual bird-walk page associates this URL with magpie chatter; primary YouTube metadata remains a runtime acquisition coordinate"
  "video-id paid; runtime title/channel/media metadata not yet retained here"

unresolvedSeed : YouTubeSeedSource
unresolvedSeed = youtube-seed-source
  "8u_7lFB5iLg"
  "https://www.youtube.com/watch?v=8u_7lFB5iLg"
  "candidate audiovisual birdsong/performance source"
  "unresolved"
  "no verified external metadata located in the current source pass; do not guess title, species or behaviour"
  "video-id paid; title/species/role details unresolved pending runtime metadata"

magpieSingingSeed : YouTubeSeedSource
magpieSingingSeed = youtube-seed-source
  "oYEYc8Ge3nw"
  "https://www.youtube.com/watch?v=oYEYc8Ge3nw"
  "candidate audiovisual source for song/acoustic-versus-visible-body analysis"
  "Australian magpie singing"
  "Western Australia Department of Education and independent reference pages identify this URL as Australian magpie singing"
  "video-id and bounded external label paid; runtime media metadata remains separate"

currentYouTubeSeeds : List YouTubeSeedSource
currentYouTubeSeeds = magpieChatterSeed ∷ unresolvedSeed ∷ magpieSingingSeed ∷ []

animalexicRuntimeOwner : String
animalexicRuntimeOwner = "scripts/run_stereo_dispatch.py:FrameStreamer"

animalexicSeedAdapter : String
animalexicSeedAdapter = "scripts/youtube_birdsong_candidate_adapter.py"

record YouTubeSeedBoundary : Set where
  constructor youtube-seed-boundary
  field
    URLImpliesStableMediaBytes : Bool
    externalLabelImpliesVerifiedSpeciesIdentity : Bool
    rawAudioAmplitudeIsCalibratedSPL : Bool
    rawAudioEnergyIsMetabolicEnergy : Bool
    visibleMotionIsBiomechanicalWork : Bool
    videoRevealsHeartRate : Bool
    videoRevealsMetabolicPower : Bool
    sharedAVTimelineCreatesCausality : Bool
    publicYouTubeSourceCreatesAnimalexicPromotion : Bool
    transientSourcePTSCanSupportCandidateTemporalAnalysis : Bool
    missingMetadataMustRemainUnresolved : Bool

open YouTubeSeedBoundary public

canonicalYouTubeSeedBoundary : YouTubeSeedBoundary
canonicalYouTubeSeedBoundary = youtube-seed-boundary
  false false false false false false false false false true true

sourceUseReading : String
sourceUseReading =
  "These YouTube URLs are candidate audiovisual acquisition surfaces. Existing Animalexic machinery can resolve and stream source frames without requiring a full download and retains source-relative frame time. Later audio/video feature producers may ask pitch, spectrum, amplitude proxy, visible movement or lag questions, but calibrated SPL, metabolic power, heart rate, species identity and causality remain separate unpaid coordinates."
