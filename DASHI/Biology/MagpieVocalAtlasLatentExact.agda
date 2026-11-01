module DASHI.Biology.MagpieVocalAtlasLatentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.MagpieVocalAtlasObservationExact as Observation

------------------------------------------------------------------------
-- HIERARCHICAL / FACTORISED MAGPIE VOCAL LATENT ATLAS
--
-- The latent object is deliberately not a single opaque "meaning vector".
-- Acoustic form, semantics/function, geography, group syntax, individual voice,
-- situated context/environment and recording provenance remain independently
-- nameable fibres and therefore independently reopenable obligations.
------------------------------------------------------------------------

data MagpieLatentFibre : Set where
  acousticForm : MagpieLatentFibre
  semanticCore : MagpieLatentFibre
  geographicRealisation : MagpieLatentFibre
  groupSyntax : MagpieLatentFibre
  individualVoice : MagpieLatentFibre
  situatedContext : MagpieLatentFibre
  environment : MagpieLatentFibre
  recordingProvenance : MagpieLatentFibre

allLatentFibres : List MagpieLatentFibre
allLatentFibres =
  acousticForm ∷ semanticCore ∷ geographicRealisation ∷ groupSyntax ∷
  individualVoice ∷ situatedContext ∷ environment ∷ recordingProvenance ∷ []

data AtlasQuery : Set where
  acousticNearestNeighbour : AtlasQuery
  sameCallFamily : AtlasQuery
  sameGroupSequence : AtlasQuery
  regionalRealisation : AtlasQuery
  individualVoiceComparison : AtlasQuery
  semanticFamily : AtlasQuery
  provenanceAudit : AtlasQuery
  dialectStatus : AtlasQuery

data AtlasAnswer : Set where
  sameFamily : AtlasAnswer
  differentFamily : AtlasAnswer
  dialectSupported : AtlasAnswer
  dialectNotSupported : AtlasAnswer
  unresolved : AtlasAnswer

------------------------------------------------------------------------
-- Finite obstruction 1: equal latent/acoustic similarity does not determine
-- semantic identity.
------------------------------------------------------------------------

data SemanticDemoState : Set where
  sameAcousticsGreetingContext : SemanticDemoState
  sameAcousticsAlarmContext : SemanticDemoState

data AcousticSimilaritySurface : Set where
  sameLatentAcousticNeighbourhood : AcousticSimilaritySurface

acousticSimilarityProjection : SemanticDemoState → AcousticSimilaritySurface
acousticSimilarityProjection state = sameLatentAcousticNeighbourhood

semanticDemoAnswer : AtlasQuery → SemanticDemoState → AtlasAnswer
semanticDemoAnswer semanticFamily sameAcousticsGreetingContext = sameFamily
semanticDemoAnswer semanticFamily sameAcousticsAlarmContext = differentFamily
semanticDemoAnswer query state = unresolved

semanticDemoSemantics : Query.QuerySemantics SemanticDemoState AtlasQuery AtlasAnswer
semanticDemoSemantics = Query.querySemantics semanticDemoAnswer

latentSimilaritySemanticDefect :
  Query.QueryAdequacyDefect
    acousticSimilarityProjection semanticDemoSemantics semanticFamily
latentSimilaritySemanticDefect =
  Query.queryAdequacyDefect
    sameAcousticsGreetingContext
    sameAcousticsAlarmContext
    refl
    (λ ())

latentSimilarityDoesNotCreateMeaning :
  Query.AdequateFor
    acousticSimilarityProjection semanticDemoSemantics semanticFamily → ⊥
latentSimilarityDoesNotCreateMeaning =
  Query.queryAdequacyDefectBlocksFactorisation latentSimilaritySemanticDefect

------------------------------------------------------------------------
-- Finite obstruction 2: a classifier can predict region for reasons that have
-- nothing to do with biological dialect (channel, codec, background species,
-- habitat soundscape, sampling design, etc.).  Therefore region-predictability
-- alone cannot pay dialect status.
------------------------------------------------------------------------

data DialectDemoState : Set where
  regionPredictableBiologicalDifference : DialectDemoState
  regionPredictableRecordingConfound : DialectDemoState

data RegionPredictabilitySurface : Set where
  regionPredictable : RegionPredictabilitySurface

regionPredictabilityProjection : DialectDemoState → RegionPredictabilitySurface
regionPredictabilityProjection state = regionPredictable

dialectDemoAnswer : AtlasQuery → DialectDemoState → AtlasAnswer
dialectDemoAnswer dialectStatus regionPredictableBiologicalDifference = dialectSupported
dialectDemoAnswer dialectStatus regionPredictableRecordingConfound = dialectNotSupported
dialectDemoAnswer query state = unresolved

dialectDemoSemantics : Query.QuerySemantics DialectDemoState AtlasQuery AtlasAnswer
dialectDemoSemantics = Query.querySemantics dialectDemoAnswer

regionPredictabilityDialectDefect :
  Query.QueryAdequacyDefect
    regionPredictabilityProjection dialectDemoSemantics dialectStatus
regionPredictabilityDialectDefect =
  Query.queryAdequacyDefect
    regionPredictableBiologicalDifference
    regionPredictableRecordingConfound
    refl
    (λ ())

regionPredictabilityDoesNotCreateDialect :
  Query.AdequateFor
    regionPredictabilityProjection dialectDemoSemantics dialectStatus → ⊥
regionPredictabilityDoesNotCreateDialect =
  Query.queryAdequacyDefectBlocksFactorisation regionPredictabilityDialectDefect

record MagpieLatentAtlasBoundary : Set where
  constructor magpie-latent-atlas-boundary
  field
    noSingleScalarMeaningScore : Bool
    latentSimilarityDoesNotCreateSemanticIdentity : Bool
    sameAcousticClusterDoesNotCreateSameFunction : Bool
    groupSyntaxDoesNotCreateRegionalDialect : Bool
    channelUploaderPredictabilityDoesNotCreatePopulationEffect : Bool
    backgroundSpeciesOrNoiseDoesNotCreateDialect : Bool
    codecOrMicrophoneSignatureDoesNotCreateDialect : Bool
    individualIdentityDoesNotCreateRegionalAccent : Bool
    semanticInvarianceDoesNotCreateAcousticInvariance : Bool
    acousticInvarianceDoesNotCreateSemanticInvariance : Bool
    consumerAdequacyRemainsQueryIndexed : Bool
    recordingProvenanceRemainsRecoverable : Bool
    environmentRemainsRecoverable : Bool

open MagpieLatentAtlasBoundary public

canonicalMagpieLatentAtlasBoundary : MagpieLatentAtlasBoundary
canonicalMagpieLatentAtlasBoundary =
  magpie-latent-atlas-boundary
    true true true true true true true true true true true true true

observationOwnerReused : String
observationOwnerReused = "DASHI.Biology.MagpieVocalAtlasObservationExact"

queryIndexedAdequacyOwnerReused : String
queryIndexedAdequacyOwnerReused = "DASHI.Core.QueryIndexedProjectionAdequacyExact"

latentAtlasReading : String
latentAtlasReading =
  "The magpie atlas separates acoustic form, semantic/function hypotheses, geographic realization, group syntax, individual voice, situated context, environment and recording provenance. Acoustic similarity may be useful for retrieval while being formally inadequate for semantic identity; region predictability may be useful for discovery while being formally inadequate for dialect status."
