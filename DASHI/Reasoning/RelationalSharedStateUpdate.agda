module DASHI.Reasoning.RelationalSharedStateUpdate where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationalStateCore as Core

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Shared-state update.
--
-- A contribution can be acoustically heard without being retained in the
-- jointly maintained state.  Uptake is represented separately from hearing.
------------------------------------------------------------------------

data Heard : Core.Contribution → Set where
  acousticallyRegistered :
    (c : Core.Contribution) → Heard c

------------------------------------------------------------------------
-- Exact contribution disposition.
------------------------------------------------------------------------

data ContributionDisposition
    (c : Core.Contribution)
    (after : Core.SharedState) : Set where
  nonQuestionRetained :
    Core.contributionKind c ≢ Core.questionContribution →
    ContributionDisposition c after
  questionRemainsOpen :
    Core.Member
      (Core.contributionLabel c)
      (Core.unresolvedQuestions after) →
    ContributionDisposition c after
  questionResolvedByAssent :
    Core.Member
      (Core.contributionLabel c)
      (Core.recordedAssents after) →
    ContributionDisposition c after
  questionResolvedByRefusal :
    Core.Member
      (Core.contributionLabel c)
      (Core.recordedRefusals after) →
    ContributionDisposition c after

data DurablePreferenceTransition
    (c : Core.Contribution)
    (before after : Core.SharedState) : Set where
  noPreferenceInsertion :
    Core.contributionKind c ≢ Core.preferenceContribution →
    Core.durablePreferences after ≡ Core.durablePreferences before →
    DurablePreferenceTransition c before after
  insertDurablePreference :
    (preference : Core.DurablePreference) →
    Core.contributionKind c ≡ Core.preferenceContribution →
    Core.preferenceOwner preference ≡ Core.contributor c →
    Core.preferenceLabel preference ≡ Core.contributionLabel c →
    Core.durablePreferences after
      ≡ preference ∷ Core.durablePreferences before →
    DurablePreferenceTransition c before after

record DecisionHistoryTransition
    (before after : Core.SharedState) : Set where
  constructor decisionHistoryTransition
  field
    priorDecisionRetained :
      Core.Member
        (Core.currentDecisionRecord before)
        (Core.decisionHistory after)
    currentDecisionRetained :
      Core.Member
        (Core.currentDecisionRecord after)
        (Core.decisionHistory after)
    decisionTransitionReceipt : String

open DecisionHistoryTransition public

record ContributionTransition
    (c : Core.Contribution)
    (before after : Core.SharedState) : Set where
  constructor contributionTransition
  field
    contributionHistoryTransition :
      Core.contributions after ≡ c ∷ Core.contributions before
    contributionDisposition : ContributionDisposition c after
    preferenceTransition : DurablePreferenceTransition c before after
    decisionTransition : DecisionHistoryTransition before after
    transitionReceipt : String

open ContributionTransition public

record Uptaken
    (c : Core.Contribution)
    (before after : Core.SharedState) : Set where
  constructor uptaken
  field
    registered : Heard c
    stateTransition : ContributionTransition c before after
    uptakeReceipt : String

open Uptaken public

record HeardWithoutUptake
    (c : Core.Contribution)
    (before after : Core.SharedState) : Set where
  constructor heardWithoutUptake
  field
    heard : Heard c
    contributionNotInserted :
      (Core.contributions after ≡ c ∷ Core.contributions before) → ⊥
    receipt : String

open HeardWithoutUptake public

record ObjectDisplacement
    (c : Core.Contribution)
    (before after : Core.SharedState) : Set where
  constructor objectDisplacement
  field
    replacementObject : Core.Topic
    replacementBecameOperative : Core.currentObject after ≡ replacementObject
    contributionNotRetained :
      Core.Member c (Core.contributions after) → ⊥
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

------------------------------------------------------------------------
-- Future obligation evidence.
------------------------------------------------------------------------

record ExplicitCommitmentEvidence
    (participant : Core.Participant)
    (obligation : String) : Set where
  constructor explicitCommitmentEvidence
  field
    sourceRepresentation : Core.TypedRepresentation
    ownerMatches :
      Core.representationOwner sourceRepresentation ≡ participant
    representationIsCommitment :
      Core.representationType sourceRepresentation
      ≡ Core.commitmentRepresentation
    obligationMatches :
      Core.representationLabel sourceRepresentation ≡ obligation

open ExplicitCommitmentEvidence public

record FutureObligation
    (participant : Core.Participant)
    (obligation : String) : Set where
  constructor futureObligation
  field
    commitmentEvidence : ExplicitCommitmentEvidence participant obligation
    futureCapacity : Core.CapacityState
    obligationReceipt : String

open FutureObligation public

futureObligationRequiresExplicitCommitment :
  {participant : Core.Participant} →
  {obligation : String} →
  FutureObligation participant obligation →
  ExplicitCommitmentEvidence participant obligation
futureObligationRequiresExplicitCommitment = commitmentEvidence

record FutureCapacityCapture : Set where
  constructor futureCapacityCapture
  field
    decisionMaker labourBearer : Core.Participant
    presentInteraction : String
    laterAttributedCommitment : String
    noExplicitCommitment :
      ExplicitCommitmentEvidence labourBearer laterAttributedCommitment → ⊥
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
    uptakeRequiresContributionTransition : Bool
    durablePreferenceRequiresExplicitTransition : Bool

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
  ; uptakeRequiresContributionTransition = true
  ; durablePreferenceRequiresExplicitTransition = true
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
