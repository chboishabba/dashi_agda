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

data Member {A : Set} (x : A) : List A → Set where
  memberHere : ∀ {xs} → Member x (x ∷ xs)
  memberThere : ∀ {y xs} → Member x xs → Member x (y ∷ xs)

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
  commitmentRepresentation : RepresentationType
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

------------------------------------------------------------------------
-- Durable preference and decision-history state.
------------------------------------------------------------------------

record DurablePreference : Set where
  constructor durablePreference
  field
    preferenceOwner : Participant
    preferenceLabel : String
    preferenceScope : String
    preferenceTime : String
    preferenceProvenance : String

open DurablePreference public

record DecisionRecord : Set where
  constructor decisionRecord
  field
    recordedDecisionKind : DecisionKind
    recordedDecisionProvenance : String

open DecisionRecord public

record SharedState : Set where
  constructor sharedState
  field
    currentObject : Topic
    contributions : List Contribution
    durablePreferences : List DurablePreference
    unresolvedQuestions : List String
    recordedAssents : List String
    recordedRefusals : List String
    decisionKind : DecisionKind
    decisionProvenance : String
    decisionHistory : List DecisionRecord
    attributedFutureObligations : List String
    ruptureStatus : RuptureStatus
    stateReceipt : String

open SharedState public

currentDecisionRecord : SharedState → DecisionRecord
currentDecisionRecord state =
  decisionRecord (decisionKind state) (decisionProvenance state)

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
    preferenceContributionAutomaticallyBecomesDurable : Bool
    careAutomaticallyCancelsMisconduct : Bool
    currentAccountErasesPriorProvenance : Bool
    abstractionAppliesOnlyToOneFamily : Bool
    boundaryNote : String

canonicalRelationalStateAuthorityBoundary : RelationalStateAuthorityBoundary
canonicalRelationalStateAuthorityBoundary = record
  { rolesAreDiagnoses = false
  ; feelingsAutomaticallyBecomeFacts = false
  ; preferenceContributionAutomaticallyBecomesDurable = false
  ; careAutomaticallyCancelsMisconduct = false
  ; currentAccountErasesPriorProvenance = false
  ; abstractionAppliesOnlyToOneFamily = false
  ; boundaryNote =
      "The vocabulary is a typed carrier for reconstructing relational episodes. Durable preferences and decision history require explicit owner, scope, time and provenance; the model does not infer motive, diagnosis, guilt or family identity without incident-specific evidence."
  }
