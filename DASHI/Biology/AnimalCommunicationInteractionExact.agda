module DASHI.Biology.AnimalCommunicationInteractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.AnimalCommunicationSceneObservationExact as Scene

------------------------------------------------------------------------
-- SENDER / ADDRESSEE / RECEIVER-RESPONSE / TURN STRUCTURE
------------------------------------------------------------------------

data ReceiverSetStatus : Set where
  noReceiverObserved : ReceiverSetStatus
  singletonReceiverCandidate : ReceiverSetStatus
  multipleReceiverCandidates : ReceiverSetStatus
  receiverSetUnresolved : ReceiverSetStatus

data ResponseType : Set where
  vocalResponse : ResponseType
  movementPostureResponse : ResponseType
  approachResponse : ResponseType
  withdrawalResponse : ResponseType
  vigilanceResponse : ResponseType
  feedingForagingResponse : ResponseType
  groupReconfigurationResponse : ResponseType
  humanActionResponse : ResponseType
  noDetectedResponse : ResponseType
  unresolvedResponse : ResponseType

record ReceiverResponse : Set where
  constructor receiver-response
  field
    receiverReferences : List String
    receiverSetStatus : ReceiverSetStatus
    responseType : ResponseType
    responseStartReference : String
    responseEndReference : String
    observationCoverageReference : String
    provenanceReference : String
    decision : Scene.ObservationDecision

open ReceiverResponse public

record InteractionTurn : Set where
  constructor interaction-turn
  field
    turnId : String
    sceneReference : String
    senderReference : String
    receiverReferences : List String
    receiverStatus : ReceiverSetStatus
    signalReference : String
    signalModality : Scene.SignalModality
    preStateReference : String
    receiverResponse : ReceiverResponse
    deltaTimeReference : String
    nextTurnReference : String
    contextReference : String
    provenanceReference : String

open InteractionTurn public

data InteractionRelation : Set where
  emittedBy : InteractionRelation
  directedToCandidate : InteractionRelation
  followedBy : InteractionRelation
  respondedToCandidate : InteractionRelation
  overlapsWith : InteractionRelation
  sameBoutEpisode : InteractionRelation
  sameGroupCandidate : InteractionRelation
  sameSourceTrackCandidate : InteractionRelation

------------------------------------------------------------------------
-- Same signal form can be addressed differently.
------------------------------------------------------------------------

data AddresseeState : Set where
  sameSignalToMate : AddresseeState
  sameSignalToNeighbour : AddresseeState

data SignalFormSurface : Set where sameSignalForm : SignalFormSurface
data AddresseeQuery : Set where signalFormQuery addresseeQuery : AddresseeQuery
data AddresseeAnswer : Set where sameFormAnswer mateAnswer neighbourAnswer : AddresseeAnswer

signalFormProjection : AddresseeState → SignalFormSurface
signalFormProjection state = sameSignalForm

addresseeAnswer : AddresseeQuery → AddresseeState → AddresseeAnswer
addresseeAnswer signalFormQuery state = sameFormAnswer
addresseeAnswer addresseeQuery sameSignalToMate = mateAnswer
addresseeAnswer addresseeQuery sameSignalToNeighbour = neighbourAnswer

addresseeSemantics : Query.QuerySemantics AddresseeState AddresseeQuery AddresseeAnswer
addresseeSemantics = Query.querySemantics addresseeAnswer

signalFormAddresseeDefect :
  Query.QueryAdequacyDefect signalFormProjection addresseeSemantics addresseeQuery
signalFormAddresseeDefect =
  Query.queryAdequacyDefect sameSignalToMate sameSignalToNeighbour refl (λ ())

signalFormCannotDetermineAddressee :
  Query.AdequateFor signalFormProjection addresseeSemantics addresseeQuery → ⊥
signalFormCannotDetermineAddressee =
  Query.queryAdequacyDefectBlocksFactorisation signalFormAddresseeDefect

------------------------------------------------------------------------
-- Same signal/context surface can lead to different observed receiver response.
------------------------------------------------------------------------

data ResponseState : Set where approachWorld withdrawalWorld : ResponseState
data SignalContextSurface : Set where sameSignalContext : SignalContextSurface
data ResponseQuery : Set where contextQuery responseQuery : ResponseQuery
data ResponseAnswer : Set where sameContextAnswer approachAnswer withdrawalAnswer : ResponseAnswer

signalContextProjection : ResponseState → SignalContextSurface
signalContextProjection state = sameSignalContext

responseAnswer : ResponseQuery → ResponseState → ResponseAnswer
responseAnswer contextQuery state = sameContextAnswer
responseAnswer responseQuery approachWorld = approachAnswer
responseAnswer responseQuery withdrawalWorld = withdrawalAnswer

responseSemantics : Query.QuerySemantics ResponseState ResponseQuery ResponseAnswer
responseSemantics = Query.querySemantics responseAnswer

signalContextResponseDefect :
  Query.QueryAdequacyDefect signalContextProjection responseSemantics responseQuery
signalContextResponseDefect =
  Query.queryAdequacyDefect approachWorld withdrawalWorld refl (λ ())

signalContextCannotDetermineResponse :
  Query.AdequateFor signalContextProjection responseSemantics responseQuery → ⊥
signalContextCannotDetermineResponse =
  Query.queryAdequacyDefectBlocksFactorisation signalContextResponseDefect

record InteractionBoundary : Set where
  constructor interaction-boundary
  field
    noDetectedResponseImpliesNoResponse : Bool
    observationCoverageRequiredForNegativeResponseClaim : Bool
    coOccurrenceImpliesAddressee : Bool
    followedByImpliesRespondedTo : Bool
    responseCorrelationCreatesCausalMechanism : Bool
    receiverResponseIsFirstClassObservation : Bool
    addresseeIdentityIsFirstClassCoordinate : Bool
    interactionTurnOrderingIsFirstClassCoordinate : Bool

open InteractionBoundary public

canonicalInteractionBoundary : InteractionBoundary
canonicalInteractionBoundary =
  interaction-boundary false true false false false true true true
