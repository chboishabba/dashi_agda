module DASHI.Reasoning.RelationalStateCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Abstract relational vocabulary.
--
-- The core deliberately names roles rather than particular people.  A
-- participant may occupy more than one role over time; no constructor is a
-- psychological diagnosis or a moral verdict.
------------------------------------------------------------------------

data RelationalRole : Set where
  parentRole childRole caregiverRole dependentRole : RelationalRole
  siblingRole grandparentRole clinicianRole thirdPartyRole : RelationalRole

record Participant : Set where
  constructor participant
  field
    participantLabel : String
    participantRole : RelationalRole

open Participant public

data Topic : Set where
  storyTopic practicalTopic planningTopic agreementTopic : Topic
  allegationTopic ruptureTopic repairTopic familyHistoryTopic : Topic

data ContributionKind : Set where
  storyContribution questionContribution preferenceContribution : ContributionKind
  proposalContribution objectionContribution clarificationContribution : ContributionKind
  allegationContribution repairContribution withdrawalContribution : ContributionKind

record Contribution : Set where
  constructor contribution
  field
    contributor : Participant
    contributionKind : ContributionKind
    contributionLabel : String

open Contribution public

data RepresentationType : Set where
  presentFeeling presentPreference rememberedEvent attributedIntention : RepresentationType
  expressedPreference proposalRepresentation assentRepresentation : RepresentationType
  unilateralDecisionRepresentation jointAgreementRepresentation : RepresentationType
  publicFactRepresentation unresolvedRepresentation : RepresentationType

data DecisionKind : Set where
  noDecision unilateralDecision jointDecision deferredDecision : DecisionKind

data RuptureStatus : Set where
  noRupture ruptureOpen ruptureAcknowledged ruptureRepaired : RuptureStatus

data Stance : Set where
  rejectStance openStance affirmStance : Stance

data ZeroKind : Set where
  absentZero openZero suspendedZero cancelledZero : ZeroKind
  expiredUnweighedZero completedNeutralZero blockedZero handoverZero : ZeroKind

data DeliberativeStatus : Set where
  notOpen openOption consideringOption : DeliberativeStatus

data SelectionStatus : Set where
  noPreference preferOption intendOption selectedOption : SelectionStatus

data ObligationStatus : Set where
  noObligation proposedObligation acceptedCommitment revokedCommitment : ObligationStatus

record CapacityState : Set where
  constructor capacityState
  field
    availableUnits : Nat
    requiredUnits : Nat
    capacityLabel : String

open CapacityState public

record SharedState : Set where
  constructor sharedState
  field
    currentObject : Topic
    contributions : List Contribution
    unresolvedQuestions : List String
    recordedAssents : List String
    recordedRefusals : List String
    decisionKind : DecisionKind
    decisionProvenance : String
    attributedFutureObligations : List String
    ruptureStatus : RuptureStatus
    stateReceipt : String

open SharedState public

record TypedRepresentation : Set where
  constructor typedRepresentation
  field
    representationOwner : Participant
    representationType : RepresentationType
    representationLabel : String
    provenance : String

open TypedRepresentation public

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record RelationalStateAuthorityBoundary : Set where
  field
    rolesAreDiagnoses : Bool
    feelingsAutomaticallyBecomeFacts : Bool
    careAutomaticallyCancelsMisconduct : Bool
    currentAccountErasesPriorProvenance : Bool
    abstractionAppliesOnlyToOneFamily : Bool
    boundaryNote : String

canonicalRelationalStateAuthorityBoundary : RelationalStateAuthorityBoundary
canonicalRelationalStateAuthorityBoundary = record
  { rolesAreDiagnoses = false
  ; feelingsAutomaticallyBecomeFacts = false
  ; careAutomaticallyCancelsMisconduct = false
  ; currentAccountErasesPriorProvenance = false
  ; abstractionAppliesOnlyToOneFamily = false
  ; boundaryNote =
      "The vocabulary is a typed carrier for reconstructing relational episodes. It does not infer motive, diagnosis, guilt or family identity without incident-specific evidence."
  }
