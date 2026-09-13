module DASHI.Biology.BioacousticMultimodalLagFactorisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Consumer
import DASHI.Biology.BioacousticMultimodalEpisodeTrajectoryExact as Episode

------------------------------------------------------------------------
-- CONSUMER-RELATIVE MULTIMODAL LAG / FACTORISATION
--
-- The same synchronized episode carrier can be adequate for one question and
-- inadequate for another.  Lag/conditional questions must therefore declare
-- their target, controls, source channels and same-episode requirement.  This
-- module reuses QueryIndexedProjectionAdequacyExact rather than inventing a
-- second adequacy calculus.
------------------------------------------------------------------------

data MultimodalQuery : Set where
  heartRateLeadsTempo : MultimodalQuery
  pressurePredictsSPLGivenPitch : MultimodalQuery
  danceAddsEnergeticLoadGivenSong : MultimodalQuery
  acousticallySimilarDifferentPhysiology : MultimodalQuery

data QueryAnswer : Set where
  supported : QueryAnswer
  notSupported : QueryAnswer
  unresolved : QueryAnswer

record LaggedConsumerRequest : Set where
  constructor lagged-consumer-request
  field
    query : MultimodalQuery
    predictorChannels : List String
    targetChannels : List String
    controlCoordinates : List String
    lagWindowReference : String
    episodeIdentityReference : String
    alignmentReceiptReference : String
    sameEpisodeRequired : Bool
    controlCoordinatesRetained : Bool
    sourceProvenanceRetained : Bool
    missingChannelForcesUnresolved : Bool

open LaggedConsumerRequest public

heartRateTempoRequest : LaggedConsumerRequest
heartRateTempoRequest = lagged-consumer-request
  heartRateLeadsTempo
  ("cardiac" ∷ [])
  ("acoustic-tempo" ∷ [])
  ("social-context" ∷ "song-bout identity" ∷ [])
  "consumer-declared signed lag window on the paid episode clock"
  "same synchronized song episode"
  "MultimodalEpisodeClockReceipt"
  true true true true

pressureSPLGivenPitchRequest : LaggedConsumerRequest
pressureSPLGivenPitchRequest = lagged-consumer-request
  pressurePredictsSPLGivenPitch
  ("respiratory-pressure" ∷ [])
  ("sound-pressure-level" ∷ [])
  ("pitch/fundamental-frequency" ∷ "microphone calibration" ∷ [])
  "consumer-declared signed lag window on the paid episode clock"
  "same synchronized song episode"
  "MultimodalEpisodeClockReceipt"
  true true true true

danceEnergyGivenSongRequest : LaggedConsumerRequest
danceEnergyGivenSongRequest = lagged-consumer-request
  danceAddsEnergeticLoadGivenSong
  ("movement/dance" ∷ [])
  ("whole-animal metabolic-power" ∷ "accumulated-excess-energy" ∷ [])
  ("song-production state" ∷ "baseline activity" ∷ "social-context" ∷ [])
  "consumer-declared signed lag / integration window on the paid episode clock"
  "same synchronized display episode"
  "MultimodalEpisodeClockReceipt"
  true true true true

acousticSimilarityPhysiologyRequest : LaggedConsumerRequest
acousticSimilarityPhysiologyRequest = lagged-consumer-request
  acousticallySimilarDifferentPhysiology
  ("acoustic feature/embedding" ∷ [])
  ("respiratory" ∷ "cardiac" ∷ "energetic" ∷ [])
  ("species/individual" ∷ "social-context" ∷ "episode-time" ∷ [])
  "same-time or consumer-declared neighbourhood on the paid episode clock"
  "same synchronized song episode"
  "MultimodalEpisodeClockReceipt"
  true true true true

currentLaggedRequests : List LaggedConsumerRequest
currentLaggedRequests =
  heartRateTempoRequest ∷
  pressureSPLGivenPitchRequest ∷
  danceEnergyGivenSongRequest ∷
  acousticSimilarityPhysiologyRequest ∷ []

------------------------------------------------------------------------
-- Finite query-indexed adequacy witness.
--
-- Two episode states intentionally collide under an acoustic-only observer.
-- They answer the cardiac-lag and dance-energy questions differently.  Hence
-- acoustic observation alone is inadequate for those consumers even though a
-- richer/full observer can be adequate for the same finite semantics.
------------------------------------------------------------------------

data DemoEpisodeState : Set where
  acousticMatchLowCardiacDance : DemoEpisodeState
  acousticMatchHighCardiacDance : DemoEpisodeState

data AcousticOnlyObservation : Set where
  sameAcousticSurface : AcousticOnlyObservation

acousticOnly : DemoEpisodeState → AcousticOnlyObservation
acousticOnly acousticMatchLowCardiacDance = sameAcousticSurface
acousticOnly acousticMatchHighCardiacDance = sameAcousticSurface

queryAnswer : MultimodalQuery → DemoEpisodeState → QueryAnswer
queryAnswer heartRateLeadsTempo acousticMatchLowCardiacDance = notSupported
queryAnswer heartRateLeadsTempo acousticMatchHighCardiacDance = supported
queryAnswer pressurePredictsSPLGivenPitch acousticMatchLowCardiacDance = unresolved
queryAnswer pressurePredictsSPLGivenPitch acousticMatchHighCardiacDance = unresolved
queryAnswer danceAddsEnergeticLoadGivenSong acousticMatchLowCardiacDance = notSupported
queryAnswer danceAddsEnergeticLoadGivenSong acousticMatchHighCardiacDance = supported
queryAnswer acousticallySimilarDifferentPhysiology acousticMatchLowCardiacDance = supported
queryAnswer acousticallySimilarDifferentPhysiology acousticMatchHighCardiacDance = supported

multimodalSemantics :
  Query.QuerySemantics DemoEpisodeState MultimodalQuery QueryAnswer
multimodalSemantics = Query.querySemantics queryAnswer

acousticOnlyHeartRateLagDefect :
  Query.QueryAdequacyDefect acousticOnly multimodalSemantics heartRateLeadsTempo
acousticOnlyHeartRateLagDefect =
  Query.queryAdequacyDefect
    acousticMatchLowCardiacDance
    acousticMatchHighCardiacDance
    refl
    (λ ())

acousticOnlyDanceEnergyDefect :
  Query.QueryAdequacyDefect acousticOnly multimodalSemantics danceAddsEnergeticLoadGivenSong
acousticOnlyDanceEnergyDefect =
  Query.queryAdequacyDefect
    acousticMatchLowCardiacDance
    acousticMatchHighCardiacDance
    refl
    (λ ())

acousticOnlyCannotAnswerHeartRateLag :
  Query.AdequateFor acousticOnly multimodalSemantics heartRateLeadsTempo → ⊥
acousticOnlyCannotAnswerHeartRateLag =
  Query.queryAdequacyDefectBlocksFactorisation acousticOnlyHeartRateLagDefect

acousticOnlyCannotAnswerDanceEnergy :
  Query.AdequateFor acousticOnly multimodalSemantics danceAddsEnergeticLoadGivenSong → ⊥
acousticOnlyCannotAnswerDanceEnergy =
  Query.queryAdequacyDefectBlocksFactorisation acousticOnlyDanceEnergyDefect

fullEpisodeObservation : DemoEpisodeState → DemoEpisodeState
fullEpisodeObservation state = state

fullEpisodeAdequateFor :
  (query : MultimodalQuery) →
  Query.AdequateFor fullEpisodeObservation multimodalSemantics query
fullEpisodeAdequateFor query =
  Query.factorsForQuery
    (Query.answer multimodalSemantics query)
    (λ state → refl)

queryIndexedBoundaryReused : Query.QueryIndexedProjectionAdequacyBoundary
queryIndexedBoundaryReused = Query.canonicalQueryIndexedProjectionAdequacyBoundary

consumerIndexedBoundaryReused : Consumer.ConsumerIndexedTrajectoryFibreBoundary
consumerIndexedBoundaryReused = Consumer.canonicalConsumerIndexedTrajectoryFibreBoundary

sameEpisodeOwnerReused : String
sameEpisodeOwnerReused = "DASHI.Biology.BioacousticMultimodalEpisodeTrajectoryExact"

------------------------------------------------------------------------
-- Interpretation / promotion firewalls.
------------------------------------------------------------------------

record LagFactorisationBoundary : Set where
  constructor lag-factorisation-boundary
  field
    lagAssociationDoesNotCreateCausality : Bool
    temporalLeadDoesNotCreateMechanism : Bool
    correlationAfterControlsDoesNotCreateInterventionEffect : Bool
    sameEpisodeDoesNotCreateCrossModalIdentity : Bool
    acousticSimilarityDoesNotCreatePhysiologicalSimilarity : Bool
    heartRateLeadDoesNotCreateEnergeticCause : Bool
    pressureAssociationDoesNotMakePitchIrrelevant : Bool
    danceAssociationDoesNotEqualVocalCost : Bool
    oneQueryAdequacyDoesNotPromoteAllQueries : Bool
    omittedControlReopensConsumerAdequacy : Bool
    clockRevisionReopensLagConsumer : Bool
    sourceAndAlignmentReceiptsRemainRequired : Bool

open LagFactorisationBoundary public

canonicalLagFactorisationBoundary : LagFactorisationBoundary
canonicalLagFactorisationBoundary = lag-factorisation-boundary
  true true true true true true true true true true true true

lagFactorisationReading : String
lagFactorisationReading =
  "Multimodal lag analysis is consumer-indexed. A paid same-episode clock allows temporal ordering and conditional association queries, but adequacy depends on the requested target and retained controls. Acoustic-only projection is formally inadequate for cardiac-lag and dance-energy consumers in the finite witness; a richer observer may answer those questions without promoting lag, correlation or conditional association to causality or mechanism."
