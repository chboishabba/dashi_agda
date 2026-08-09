module DASHI.Reasoning.RelationalSharedStateUpdate where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationalStateCore as Core

------------------------------------------------------------------------
-- Shared-state update.
--
-- A contribution can be acoustically heard without being retained in the
-- jointly maintained state.  Uptake is represented separately from hearing.
------------------------------------------------------------------------

data Heard : Core.Contribution → Set where
  acousticallyRegistered :
    (c : Core.Contribution) → Heard c

data UptakeKind : Set where
  registeredOnly retainedRole constrainsLaterState : UptakeKind

record Uptaken
    (c : Core.Contribution)
    (before after : Core.SharedState) : Set where
  constructor uptaken
  field
    registered : Heard c
    retainedConversationalRole : Bool
    constrainsLaterResponses : Bool
    constrainsDecisionHistory : Bool
    uptakeReceipt : String

open Uptaken public

record HeardWithoutUptake
    (c : Core.Contribution)
    (before after : Core.SharedState) : Set where
  constructor heardWithoutUptake
  field
    heard : Heard c
    roleDiscarded : Bool
    laterConstraintLost : Bool
    receipt : String

open HeardWithoutUptake public

record ObjectDisplacement
    (c : Core.Contribution)
    (before after : Core.SharedState) : Set where
  constructor objectDisplacement
  field
    contributionStillOpen : Bool
    replacementObject : Core.Topic
    replacementBecameOperative : Bool
    originalContributionCeasedToConstrain : Bool
    displacementReceipt : String

open ObjectDisplacement public

record ConsultationEpisode : Set where
  constructor consultationEpisode
  field
    consulter consulted : Core.Participant
    proposalLabel : String
    inputLabel : String
    resultingDecision : Core.DecisionKind
    decisionSensitiveToInput : Bool
    laterNarratedAsJoint : Bool
    consultationReceipt : String

open ConsultationEpisode public

consultationDecisionSensitive : ConsultationEpisode → Bool
consultationDecisionSensitive episode =
  decisionSensitiveToInput episode

-- The following witness carries the pseudo-consultation failure pattern
-- without pretending Boolean negation is a proof.
record PseudoConsultationWitness (episode : ConsultationEpisode) : Set where
  field
    inputWasRequested : Bool
    inputWasNotDecisionSensitive : Bool
    unilateralDecisionLaterPresentedAsJoint : Bool
    witnessReceipt : String

record SilenceEpisode : Set where
  constructor silenceEpisode
  field
    silentParticipant : Core.Participant
    possibleMeanings : List String
    explicitAssentRecorded : Bool
    actionStillRequired : Bool
    correctDecisionKind : Core.DecisionKind
    silenceReceipt : String

record RuptureSignal : Set where
  constructor ruptureSignal
  field
    speaker listener : Core.Participant
    surfaceSignal : String
    encodedRupture : Core.RuptureStatus
    decodedAsVoluntaryWithdrawal : Bool
    causalChainPreserved : Bool
    signalReceipt : String

record PresentStatePromotion : Set where
  constructor presentStatePromotion
  field
    source : Core.TypedRepresentation
    promotedTargetType : Core.RepresentationType
    promotionWitnessPresent : Bool
    promotionReceipt : String

record BehaviouralAllegation : Set where
  constructor behaviouralAllegation
  field
    allegedActor affectedParticipant : Core.Participant
    allegedAct : String
    observableParticular : String
    context : String
    allegedEffect : String
    particularised : Bool
    allegationReceipt : String

record FutureCapacityCapture : Set where
  constructor futureCapacityCapture
  field
    decisionMaker labourBearer : Core.Participant
    presentInteraction : String
    laterAttributedCommitment : String
    explicitCommitmentPresent : Bool
    futureCapacity : Core.CapacityState
    captureReceipt : String

record CaregiverCreditSubstitution : Set where
  constructor caregiverCreditSubstitution
  field
    careProvider careRecipient : Core.Participant
    careProvided : String
    conductUnderReview : String
    careUsedAsAnswerToConduct : Bool
    recipientStandingReduced : Bool
    substitutionReceipt : String

------------------------------------------------------------------------
-- Repair invariants.
------------------------------------------------------------------------

record SharedStateInvariants : Set where
  field
    openContributionPersistsUntilAnsweredOrDeferred : Bool
    silenceNeverPromotedToAssentWithoutWitness : Bool
    unilateralDecisionRetainsUnilateralProvenance : Bool
    allegationsRequireParticulars : Bool
    feelingsAndFactsRemainDistinct : Bool
    rupturePersistsUntilRepairWitness : Bool
    futureObligationsRequireExplicitCommitment : Bool
    careAndAccountabilityRemainDistinct : Bool

canonicalSharedStateInvariants : SharedStateInvariants
canonicalSharedStateInvariants = record
  { openContributionPersistsUntilAnsweredOrDeferred = true
  ; silenceNeverPromotedToAssentWithoutWitness = true
  ; unilateralDecisionRetainsUnilateralProvenance = true
  ; allegationsRequireParticulars = true
  ; feelingsAndFactsRemainDistinct = true
  ; rupturePersistsUntilRepairWitness = true
  ; futureObligationsRequireExplicitCommitment = true
  ; careAndAccountabilityRemainDistinct = true
  }

record MinimalRepairProtocol : Set where
  field
    identifyOriginalObject : Bool
    reconstructExactContribution : Bool
    separateFeelingFromAllegation : Bool
    particulariseAnyAllegation : Bool
    preserveDecisionProvenance : Bool
    identifyUnresolvedRupture : Bool
    stateChangedExpectation : Bool
    permitPauseWithoutErasure : Bool

canonicalMinimalRepairProtocol : MinimalRepairProtocol
canonicalMinimalRepairProtocol = record
  { identifyOriginalObject = true
  ; reconstructExactContribution = true
  ; separateFeelingFromAllegation = true
  ; particulariseAnyAllegation = true
  ; preserveDecisionProvenance = true
  ; identifyUnresolvedRupture = true
  ; stateChangedExpectation = true
  ; permitPauseWithoutErasure = true
  }
