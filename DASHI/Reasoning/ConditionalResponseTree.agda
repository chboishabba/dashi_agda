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
-- Transport assessment versus transport authorisation.
--
-- ResponseTransportWitness is deliberately only an assessment: its Booleans
-- may report failed requirements.  AuthorisedResponseTransport is the
-- locality gate used to license transport; it requires equality proofs that
-- every relevant assessment field is true.
------------------------------------------------------------------------

record ResponseTransportWitness
    (source target : PropositionNode) : Set where
  constructor responseTransportAssessment
  field
    nodeTransportable : Bool
    contextTransportable : Bool
    modalityTransportable : Bool
    scopeTransportable : Bool
    temporalValidityRechecked : Bool
    newExplicitCommitmentWhereStrengthened : Bool
    transportReceipt : String

open ResponseTransportWitness public

record AuthorisedResponseTransport
    (source target : PropositionNode) : Set where
  constructor authorisedResponseTransport
  field
    assessment : ResponseTransportWitness source target
    nodeTransportableProof : nodeTransportable assessment ≡ true
    contextTransportableProof : contextTransportable assessment ≡ true
    modalityTransportableProof : modalityTransportable assessment ≡ true
    scopeTransportableProof : scopeTransportable assessment ≡ true
    temporalValidityProof : temporalValidityRechecked assessment ≡ true
    strengtheningCommitmentProof :
      newExplicitCommitmentWhereStrengthened assessment ≡ true
    authorisationReceipt : String

open AuthorisedResponseTransport public

transportResponse :
  {source target : PropositionNode} →
  ActualResponse →
  AuthorisedResponseTransport source target →
  PropositionNode
transportResponse {target = target} response authorisation = target

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
      "Affirmation is local to node, context, modality, scope, episode, capacity and time. An assessment may contain failed conditions; only AuthorisedResponseTransport, whose requirements are all proved true, licenses transport."
  }
