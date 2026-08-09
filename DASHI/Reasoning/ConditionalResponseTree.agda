module DASHI.Reasoning.ConditionalResponseTree where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationalStateCore as Core

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- A response attaches to an exact guarded proposition node in one decision
-- episode.  The positive trit does not determine the modality by itself.
------------------------------------------------------------------------

data Action : Set where
  converse consult decide help maintain transfer closeProcess : Action
  customAction : String → Action

data ContextAtom : Set where
  urgentContext sufficientCapacity noLessBurdensomeAlternative : ContextAtom
  boundedInstance currentAuthority liveOpportunity : ContextAtom
  customContext : String → ContextAtom

data ExceptionAtom : Set where
  revokedException unsafeException unavailableException : ExceptionAtom
  customException : String → ExceptionAtom

data Modality : Set where
  openModality considerModality preferModality intendModality : Modality
  commitModality authorisePursuitModality : Modality

consider≢commit : considerModality ≢ commitModality
consider≢commit ()

intend≢commit : intendModality ≢ commitModality
intend≢commit ()

record PropositionNode : Set where
  constructor propositionNode
  field
    nodeId : String
    antecedent : List ContextAtom
    contemplatedAction : Action
    modality : Modality
    temporalScope : String
    practicalScope : String
    exceptions : List ExceptionAtom
    unresolvedConditions : List String
    parentNodeId : String

open PropositionNode public

record DecisionToken : Set where
  constructor decisionToken
  field
    tokenId : String
    contextSnapshot : List ContextAtom
    availableAlternatives : List String
    openingTime deadline : String
    propositionVersion : Nat

open DecisionToken public

record ActualResponse : Set where
  constructor actualResponse
  field
    respondent : Core.Participant
    node : PropositionNode
    episode : DecisionToken
    responseTime : String
    stance : Core.Stance
    zeroKind : Core.ZeroKind
    deliberativeStatus : Core.DeliberativeStatus
    selectionStatus : Core.SelectionStatus
    obligationStatus : Core.ObligationStatus
    capacity : Core.CapacityState
    ownershipPresent : Bool
    refusalAvailable : Bool
    refusalSafe : Bool
    provenance : String

open ActualResponse public

------------------------------------------------------------------------
-- Exact response transport.
--
-- Transport is available only when every semantic coordinate of the source
-- node is propositionally equal to the corresponding coordinate of the target.
-- Node identifiers and parent links may differ, permitting a provenance-
-- preserving re-addressing without silently broadening context, modality,
-- scope, exceptions, or unresolved conditions.
------------------------------------------------------------------------

record ResponseTransportWitness
    (source target : PropositionNode) : Set where
  constructor responseTransportWitness
  field
    antecedentPreserved : antecedent source ≡ antecedent target
    actionPreserved : contemplatedAction source ≡ contemplatedAction target
    modalityPreserved : modality source ≡ modality target
    temporalScopePreserved : temporalScope source ≡ temporalScope target
    practicalScopePreserved : practicalScope source ≡ practicalScope target
    exceptionsPreserved : exceptions source ≡ exceptions target
    unresolvedConditionsPreserved :
      unresolvedConditions source ≡ unresolvedConditions target
    transportReceipt : String

open ResponseTransportWitness public

transportResponse :
  {source target : PropositionNode} →
  (response : ActualResponse) →
  node response ≡ source →
  ResponseTransportWitness source target →
  ActualResponse
transportResponse {target = target} response responseTargetsSource witness =
  actualResponse
    (respondent response)
    target
    (episode response)
    (responseTime response)
    (stance response)
    (zeroKind response)
    (deliberativeStatus response)
    (selectionStatus response)
    (obligationStatus response)
    (capacity response)
    (ownershipPresent response)
    (refusalAvailable response)
    (refusalSafe response)
    (provenance response)

------------------------------------------------------------------------
-- Strengthening is not transport.
--
-- A stronger modality or broader context requires a fresh response whose node
-- is definitionally tied to the target.  The old response is retained only as
-- provenance and cannot be reused as the new assent.
------------------------------------------------------------------------

record FreshStrengthenedResponse
    (source target : PropositionNode) : Set where
  constructor freshStrengthenedResponse
  field
    priorResponse : ActualResponse
    priorResponseTargetsSource : node priorResponse ≡ source
    newResponse : ActualResponse
    newResponseTargetsTarget : node newResponse ≡ target
    sameRespondent : respondent priorResponse ≡ respondent newResponse
    strengtheningReceipt : String

open FreshStrengthenedResponse public

------------------------------------------------------------------------
-- Goal-process authority.
------------------------------------------------------------------------

record GoalProcessAuthorisation : Set where
  constructor goalProcessAuthorisation
  field
    authorisedNode : PropositionNode
    authorisedStart : Bool
    boundedImplementationClosure : List Action
    authorisesEveryFutureBranch : Bool
    revocable : Bool
    processReceipt : String

record PostRevocationClassification : Set where
  constructor postRevocationClassification
  field
    alreadyCompleted : List Action
    externallyPending : List Action
    requiredClosure : List Action
    searchCapitalPreservation : List Action
    handoverOperations : List Action
    optionalContinuation : List Action
    newDiscretionaryExpansion : List Action
    classificationReceipt : String

record ResponseLocalityBoundary : Set where
  field
    parentAffirmationPropagatesToEveryDescendant : Bool
    considerationAutomaticallyBecomesCommitment : Bool
    narrowContextAutomaticallyBroadens : Bool
    oneInstanceAutomaticallyBecomesRecurringRole : Bool
    oldResponseAutomaticallyBindsLaterEpisode : Bool
    expiryAutomaticallyMeansRejection : Bool
    authoriseStartMeansAuthoriseEveryFutureStep : Bool
    laterRevocationErasesEarlierProvenance : Bool
    assessmentAloneAuthorisesTransport : Bool
    localityNote : String

canonicalResponseLocalityBoundary : ResponseLocalityBoundary
canonicalResponseLocalityBoundary = record
  { parentAffirmationPropagatesToEveryDescendant = false
  ; considerationAutomaticallyBecomesCommitment = false
  ; narrowContextAutomaticallyBroadens = false
  ; oneInstanceAutomaticallyBecomesRecurringRole = false
  ; oldResponseAutomaticallyBindsLaterEpisode = false
  ; expiryAutomaticallyMeansRejection = false
  ; authoriseStartMeansAuthoriseEveryFutureStep = false
  ; laterRevocationErasesEarlierProvenance = false
  ; assessmentAloneAuthorisesTransport = false
  ; localityNote =
      "Transport requires propositional equality of every semantic node coordinate. Any strengthening or broadening requires a fresh response explicitly indexed to the target node."
  }
