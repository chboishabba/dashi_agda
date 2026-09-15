module DASHI.Biology.AnimalCommunicationLatentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.AnimalCommunicationSceneObservationExact as Scene
import DASHI.Biology.AnimalCommunicationInteractionExact as Interaction

------------------------------------------------------------------------
-- GENERIC QUERY-INDEXED / REOPENABLE COMMUNICATION LATENT SCHEMA
------------------------------------------------------------------------

data CommunicationLatentFibre : Set where
  signalFormFibre : CommunicationLatentFibre
  senderIdentityFibre : CommunicationLatentFibre
  receiverAddresseeFibre : CommunicationLatentFibre
  interactionTurnFibre : CommunicationLatentFibre
  receiverResponseFibre : CommunicationLatentFibre
  functionalSemanticHypothesisFibre : CommunicationLatentFibre
  groupPopulationGeographicFibre : CommunicationLatentFibre
  individualRealisationFibre : CommunicationLatentFibre
  historyContextFibre : CommunicationLatentFibre
  environmentFibre : CommunicationLatentFibre
  recordingProvenanceFibre : CommunicationLatentFibre
  physicalMeasurementFibre : CommunicationLatentFibre

allCommunicationLatentFibres : List CommunicationLatentFibre
allCommunicationLatentFibres =
  signalFormFibre ∷ senderIdentityFibre ∷ receiverAddresseeFibre ∷
  interactionTurnFibre ∷ receiverResponseFibre ∷
  functionalSemanticHypothesisFibre ∷ groupPopulationGeographicFibre ∷
  individualRealisationFibre ∷ historyContextFibre ∷ environmentFibre ∷
  recordingProvenanceFibre ∷ physicalMeasurementFibre ∷ []

data CommunicationQuery : Set where
  speciesPresent : CommunicationQuery
  eventEmitter : CommunicationQuery
  eventAddressee : CommunicationQuery
  receiverResponseQuery : CommunicationQuery
  functionalClass : CommunicationQuery
  semanticClass : CommunicationQuery
  crossSpeciesStructuralAnalogy : CommunicationQuery

data CommunicationAnswer : Set where
  speciesSetKnown : CommunicationAnswer
  emitterA : CommunicationAnswer
  emitterB : CommunicationAnswer
  functionOne : CommunicationAnswer
  functionTwo : CommunicationAnswer
  semanticsOne : CommunicationAnswer
  semanticsTwo : CommunicationAnswer
  analogyPresent : CommunicationAnswer
  unresolved : CommunicationAnswer

------------------------------------------------------------------------
-- Species presence can be perfectly adequate for the scene-level species query
-- and still be inadequate for event-level emitter identity.
------------------------------------------------------------------------

data SpeciesEmitterState : Set where
  sameSceneEmitterA : SpeciesEmitterState
  sameSceneEmitterB : SpeciesEmitterState

data SpeciesPresenceObservation : Set where sameSpeciesSet : SpeciesPresenceObservation

speciesPresenceObserver : SpeciesEmitterState → SpeciesPresenceObservation
speciesPresenceObserver state = sameSpeciesSet

speciesEmitterAnswer : CommunicationQuery → SpeciesEmitterState → CommunicationAnswer
speciesEmitterAnswer speciesPresent state = speciesSetKnown
speciesEmitterAnswer eventEmitter sameSceneEmitterA = emitterA
speciesEmitterAnswer eventEmitter sameSceneEmitterB = emitterB
speciesEmitterAnswer query state = unresolved

speciesEmitterSemantics :
  Query.QuerySemantics SpeciesEmitterState CommunicationQuery CommunicationAnswer
speciesEmitterSemantics = Query.querySemantics speciesEmitterAnswer

speciesPresenceAdequateForSpeciesQuery :
  Query.AdequateFor speciesPresenceObserver speciesEmitterSemantics speciesPresent
speciesPresenceAdequateForSpeciesQuery =
  Query.factorsForQuery (λ observation → speciesSetKnown) (λ state → refl)

speciesPresenceEmitterDefect :
  Query.QueryAdequacyDefect speciesPresenceObserver speciesEmitterSemantics eventEmitter
speciesPresenceEmitterDefect =
  Query.queryAdequacyDefect sameSceneEmitterA sameSceneEmitterB refl (λ ())

speciesPresenceCannotDetermineEmitter :
  Query.AdequateFor speciesPresenceObserver speciesEmitterSemantics eventEmitter → ⊥
speciesPresenceCannotDetermineEmitter =
  Query.queryAdequacyDefectBlocksFactorisation speciesPresenceEmitterDefect

------------------------------------------------------------------------
-- Even exact emitter identity is insufficient to determine communicative
-- function/semantics without interaction/context/response evidence.
------------------------------------------------------------------------

data EmitterFunctionState : Set where
  sameEmitterFunctionOne : EmitterFunctionState
  sameEmitterFunctionTwo : EmitterFunctionState

data EmitterIdentityObservation : Set where exactSameEmitter : EmitterIdentityObservation

emitterIdentityObserver : EmitterFunctionState → EmitterIdentityObservation
emitterIdentityObserver state = exactSameEmitter

emitterFunctionAnswer : CommunicationQuery → EmitterFunctionState → CommunicationAnswer
emitterFunctionAnswer eventEmitter state = emitterA
emitterFunctionAnswer functionalClass sameEmitterFunctionOne = functionOne
emitterFunctionAnswer functionalClass sameEmitterFunctionTwo = functionTwo
emitterFunctionAnswer semanticClass sameEmitterFunctionOne = semanticsOne
emitterFunctionAnswer semanticClass sameEmitterFunctionTwo = semanticsTwo
emitterFunctionAnswer query state = unresolved

emitterFunctionSemantics :
  Query.QuerySemantics EmitterFunctionState CommunicationQuery CommunicationAnswer
emitterFunctionSemantics = Query.querySemantics emitterFunctionAnswer

emitterIdentityFunctionalDefect :
  Query.QueryAdequacyDefect emitterIdentityObserver emitterFunctionSemantics functionalClass
emitterIdentityFunctionalDefect =
  Query.queryAdequacyDefect sameEmitterFunctionOne sameEmitterFunctionTwo refl (λ ())

emitterIdentityCannotDetermineFunction :
  Query.AdequateFor emitterIdentityObserver emitterFunctionSemantics functionalClass → ⊥
emitterIdentityCannotDetermineFunction =
  Query.queryAdequacyDefectBlocksFactorisation emitterIdentityFunctionalDefect

emitterIdentitySemanticDefect :
  Query.QueryAdequacyDefect emitterIdentityObserver emitterFunctionSemantics semanticClass
emitterIdentitySemanticDefect =
  Query.queryAdequacyDefect sameEmitterFunctionOne sameEmitterFunctionTwo refl (λ ())

emitterIdentityCannotDetermineSemantics :
  Query.AdequateFor emitterIdentityObserver emitterFunctionSemantics semanticClass → ⊥
emitterIdentityCannotDetermineSemantics =
  Query.queryAdequacyDefectBlocksFactorisation emitterIdentitySemanticDefect

record CrossSpeciesAnalogyBoundary : Set where
  constructor cross-species-analogy-boundary
  field
    structuralAnalogyCanBeRecorded : Bool
    crossSpeciesAnalogyDoesNotCreateSameMechanism : Bool
    crossSpeciesAnalogyDoesNotCreateSameSemantics : Bool
    crossSpeciesAnalogyDoesNotTransferEmpiricalAuthority : Bool
    speciesLocalLatentAtlasesRemainDistinct : Bool

open CrossSpeciesAnalogyBoundary public

canonicalCrossSpeciesAnalogyBoundary : CrossSpeciesAnalogyBoundary
canonicalCrossSpeciesAnalogyBoundary =
  cross-species-analogy-boundary true true true true true

record CommunicationLatentBoundary : Set where
  constructor communication-latent-boundary
  field
    oneUniversalAnimalLanguageVectorRequired : Bool
    speciesDetectionAdequacyImpliesEmitterAdequacy : Bool
    emitterAdequacyImpliesFunctionalAdequacy : Bool
    functionalAdequacyImpliesSemanticAdequacy : Bool
    oneConsumerPromotionImpliesAllConsumerPromotion : Bool
    independentlyReopenableFibresRetained : Bool

open CommunicationLatentBoundary public

canonicalCommunicationLatentBoundary : CommunicationLatentBoundary
canonicalCommunicationLatentBoundary =
  communication-latent-boundary false false false false false true
