module DASHI.Biology.BioacousticStateSpaceVisualisationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ObserverConditionedTransportBridge as Transport
import DASHI.Core.IntrospectiveVisualRoundTripExact as Visual

------------------------------------------------------------------------
-- BIOACOUSTIC STATE-SPACE VISUALISATION
--
-- The reusable carrier extracted from contemporary birdsong visualisation is
-- not a particular black-background aesthetic.  It is the typed chain
--
--   observer sample -> acoustic feature state -> embedding -> temporal history
--                   -> rendered visual object.
--
-- Each arrow is explicit so a renderer cannot silently become an acoustic,
-- taxonomic, behavioural, or causal authority.
------------------------------------------------------------------------

record VisualisationSourceReceipt : Set where
  constructor visualisationSourceReceipt
  field
    creator : String
    project : String
    stableLocator : String
    sourceRole : String

open VisualisationSourceReceipt public

seeingBirdsongSource : VisualisationSourceReceipt
seeingBirdsongSource =
  visualisationSourceReceipt
    "Lucio Arese"
    "Seeing Birdsong"
    "https://www.lucioarese.net/seeing-birdsong/"
    "bioacoustic / generative-visualisation reference; attribution does not prove any local implementation theorem"

williamJFXSource : VisualisationSourceReceipt
williamJFXSource =
  visualisationSourceReceipt
    "William JFX"
    "Synaesthetic Sanctuary"
    "https://www.instagram.com/reel/DV5K8WHiVyB/"
    "social-art reference supplied by the investigator; retained as design inspiration, not as a scientific-method receipt"

canonicalVisualisationSources : List VisualisationSourceReceipt
canonicalVisualisationSources =
  seeingBirdsongSource
  ∷ williamJFXSource
  ∷ []

------------------------------------------------------------------------
-- Generic pipeline.
--
-- The transport system is repo-native ObserverConditionedTransport.  For an
-- acoustic instance its observer can be a microphone and Sample can be a
-- waveform/window object, but this owner does not force that specialization.
------------------------------------------------------------------------

record BioacousticStateSpacePipeline
    (system : Transport.TransportSystem) : Set₁ where
  field
    FeatureState : Set
    EmbeddedPoint : Set
    HistoryState : Set
    RenderedFrame : Set

    extractFeatures : Transport.Sample system → FeatureState
    embed : FeatureState → EmbeddedPoint

    emptyHistory : HistoryState
    appendPoint : EmbeddedPoint → HistoryState → HistoryState
    renderHistory : HistoryState → RenderedFrame

    featureReading : String
    embeddingReading : String
    historyReading : String
    renderingReading : String

open BioacousticStateSpacePipeline public

record BioacousticFrameObservation
    {system : Transport.TransportSystem}
    (pipeline : BioacousticStateSpacePipeline system) : Set₁ where
  field
    sample : Transport.Sample system
    featureState : FeatureState pipeline
    embeddedPoint : EmbeddedPoint pipeline

    featureStateIsExtracted :
      featureState ≡ extractFeatures pipeline sample

    embeddedPointIsEmbedded :
      embeddedPoint ≡ embed pipeline featureState

open BioacousticFrameObservation public

record BioacousticTemporalObservation
    {system : Transport.TransportSystem}
    (pipeline : BioacousticStateSpacePipeline system) : Set₁ where
  field
    observations : List (BioacousticFrameObservation pipeline)
    history : HistoryState pipeline
    rendered : RenderedFrame pipeline
    renderedIsHistoryObservation :
      rendered ≡ renderHistory pipeline history

open BioacousticTemporalObservation public

------------------------------------------------------------------------
-- The representation class is explicit.  Visually similar reels can have
-- materially different semantics.
------------------------------------------------------------------------

data BioacousticRepresentationClass : Set where
  literalCoordinateMap : BioacousticRepresentationClass
  dimensionalReductionEmbedding : BioacousticRepresentationClass
  delayCoordinateEmbedding : BioacousticRepresentationClass
  learnedLatentEmbedding : BioacousticRepresentationClass
  generativeFeatureDrivenGeometry : BioacousticRepresentationClass

representationClassReading : BioacousticRepresentationClass → String
representationClassReading literalCoordinateMap =
  "axes directly encode declared measurements such as time/frequency/energy"
representationClassReading dimensionalReductionEmbedding =
  "axes are latent coordinates produced from a higher-dimensional acoustic feature state"
representationClassReading delayCoordinateEmbedding =
  "coordinates are delayed samples or functions of delayed samples used as a dynamical-state reconstruction"
representationClassReading learnedLatentEmbedding =
  "coordinates are learned latent variables; proximity has only the semantics separately proved for that model"
representationClassReading generativeFeatureDrivenGeometry =
  "features drive geometry or dynamics without requiring metric or physical coordinate semantics"

------------------------------------------------------------------------
-- Fail-closed interpretation boundary.
------------------------------------------------------------------------

record BioacousticVisualisationBoundary : Set where
  field
    renderedPointIsAcousticState : Bool
    renderedPointIsAcousticStateIsFalse :
      renderedPointIsAcousticState ≡ false

    embeddingDistanceIsPhysicalDistance : Bool
    embeddingDistanceIsPhysicalDistanceIsFalse :
      embeddingDistanceIsPhysicalDistance ≡ false

    visualRecurrenceIdentifiesSameSpecies : Bool
    visualRecurrenceIdentifiesSameSpeciesIsFalse :
      visualRecurrenceIdentifiesSameSpecies ≡ false

    visualRecurrenceIdentifiesSamePhysicalGenerator : Bool
    visualRecurrenceIdentifiesSamePhysicalGeneratorIsFalse :
      visualRecurrenceIdentifiesSamePhysicalGenerator ≡ false

    rendererCreatesScientificAuthority : Bool
    rendererCreatesScientificAuthorityIsFalse :
      rendererCreatesScientificAuthority ≡ false

    historyMayDependOnEarlierFrames : Bool
    historyMayDependOnEarlierFramesIsTrue :
      historyMayDependOnEarlierFrames ≡ true

    visualObserverIsDownstream : Bool
    visualObserverIsDownstreamIsTrue :
      visualObserverIsDownstream ≡ true

open BioacousticVisualisationBoundary public

canonicalBioacousticVisualisationBoundary :
  BioacousticVisualisationBoundary
canonicalBioacousticVisualisationBoundary =
  record
    { renderedPointIsAcousticState = false
    ; renderedPointIsAcousticStateIsFalse = refl
    ; embeddingDistanceIsPhysicalDistance = false
    ; embeddingDistanceIsPhysicalDistanceIsFalse = refl
    ; visualRecurrenceIdentifiesSameSpecies = false
    ; visualRecurrenceIdentifiesSameSpeciesIsFalse = refl
    ; visualRecurrenceIdentifiesSamePhysicalGenerator = false
    ; visualRecurrenceIdentifiesSamePhysicalGeneratorIsFalse = refl
    ; rendererCreatesScientificAuthority = false
    ; rendererCreatesScientificAuthorityIsFalse = refl
    ; historyMayDependOnEarlierFrames = true
    ; historyMayDependOnEarlierFramesIsTrue = refl
    ; visualObserverIsDownstream = true
    ; visualObserverIsDownstreamIsTrue = refl
    }

------------------------------------------------------------------------
-- Introspective visual-loop cross-pollination.
--
-- The existing visual round-trip owner already states that an empirical visual
-- observation is a producer unless a sound extraction contract is separately
-- proved.  This string is a navigation receipt tying that discipline to the
-- bioacoustic specialization without duplicating its finite theorem.
------------------------------------------------------------------------

visualRoundTripOwner : String
visualRoundTripOwner =
  "DASHI.Core.IntrospectiveVisualRoundTripExact"

visualRoundTripBoundary : Visual.IntrospectiveMethodBoundary
visualRoundTripBoundary = Visual.canonicalIntrospectiveMethodBoundary
