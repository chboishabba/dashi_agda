module DASHI.Governance.GuardedPropositionResponseTree where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- A response is indexed by an exact guarded proposition node, decision token,
-- version, scope, and time.  It is never a free-standing Boolean.

------------------------------------------------------------------------
-- Proposition structure.

data GuardKind : Set where
  developmentalCapacityGuard : GuardKind
  informationalGuard : GuardKind
  urgencyGuard : GuardKind
  safeRefusalGuard : GuardKind
  alternativeAvailableGuard : GuardKind
  dependencyGuard : GuardKind
  institutionalGuard : GuardKind
  temporalGuard : GuardKind
  exceptionGuard : GuardKind

data DeliberativeStatus : Set where
  unopenedDeliberation : DeliberativeStatus
  openDeliberation : DeliberativeStatus
  consideringDeliberation : DeliberativeStatus
  completedDeliberation : DeliberativeStatus

data SelectionStatus : Set where
  unselected : SelectionStatus
  preferred : SelectionStatus
  intended : SelectionStatus
  selected : SelectionStatus

data ObligationStatus : Set where
  noObligation : ObligationStatus
  selfIntentionOnly : ObligationStatus
  interpersonalCommitment : ObligationStatus

data ScopeKind : Set where
  oneInstanceScope : ScopeKind
  boundedIntervalScope : ScopeKind
  recurringScope : ScopeKind
  indefiniteScope : ScopeKind

record Modality : Set where
  constructor modality
  field
    deliberative : DeliberativeStatus
    selection : SelectionStatus
    obligation : ObligationStatus

open Modality public

record PropositionNode : Set where
  constructor propositionNode
  field
    nodeLabel : String
    antecedent : List GuardKind
    actionLabel : String
    nodeModality : Modality
    nodeScope : ScopeKind
    temporalStart : Nat
    temporalDeadline : Nat
    exceptionLabels : List String
    openQuestions : List String
    propositionVersion : Nat
    decisionToken : Nat

open PropositionNode public

------------------------------------------------------------------------
-- Branch and zero fibres.

data ZeroKind : Set where
  absentZero : ZeroKind
  openZero : ZeroKind
  suspendedZero : ZeroKind
  cancelledZero : ZeroKind
  expiredUnweighedZero : ZeroKind
  completedNeutralZero : ZeroKind

data BranchStatus : Set where
  impossibleBranch : BranchStatus
  closedBranch : BranchStatus
  liveContingentBranch : BranchStatus
  guaranteedToBeWeighedBranch : BranchStatus
  currentlyWeighedBranch : BranchStatus
  selectedBranch : BranchStatus
  rejectedBranch : BranchStatus
  deferredBranch : BranchStatus
  expiredUnweighedBranch : BranchStatus
  reinstantiatedBranch : BranchStatus

record DecisionBranch : Set where
  constructor decisionBranch
  field
    branchNode : PropositionNode
    branchStatus : BranchStatus
    branchZeroKind : ZeroKind
    parentDecisionToken : Nat
    branchProvenance : String

open DecisionBranch public

------------------------------------------------------------------------
-- Response state.

record ResponseState : Set where
  constructor responseState
  field
    stance : Trit.Trit
    zeroKind : ZeroKind
    capacityAvailable : Bool
    refusalSafe : Bool
    responseOwned : Bool
    responseProvenance : String

open ResponseState public

record ActualResponse
  (node : PropositionNode)
  (response : ResponseState) : Set where
  constructor actualResponse
  field
    exactNodePresented : Bool
    exactNodePresentedIsTrue : exactNodePresented ≡ true

    adequatelyUnderstood : Bool
    adequatelyUnderstoodIsTrue : adequatelyUnderstood ≡ true

    ownershipWitnessed : Bool
    ownershipWitnessedIsTrue : ownershipWitnessed ≡ true

    capacityWitnessed : capacityAvailable response ≡ true
    safeRefusalWitnessed : refusalSafe response ≡ true

    provenanceValidated : Bool
    provenanceValidatedIsTrue : provenanceValidated ≡ true

open ActualResponse public

------------------------------------------------------------------------
-- Transport is fail-closed. Every semantic dimension receives its own
-- witness; no constructor silently weakens context or strengthens modality.

record ResponseTransportWitness
  (source target : PropositionNode) : Set where
  constructor responseTransportWitness
  field
    descendantTransportWitnessed : Bool
    descendantTransportWitnessedIsTrue : descendantTransportWitnessed ≡ true
    contextTransportWitnessed : Bool
    contextTransportWitnessedIsTrue : contextTransportWitnessed ≡ true
    modalityTransportWitnessed : Bool
    modalityTransportWitnessedIsTrue : modalityTransportWitnessed ≡ true
    scopeTransportWitnessed : Bool
    scopeTransportWitnessedIsTrue : scopeTransportWitnessed ≡ true
    temporalTransportWitnessed : Bool
    temporalTransportWitnessedIsTrue : temporalTransportWitnessed ≡ true
    versionTransportWitnessed : Bool
    versionTransportWitnessedIsTrue : versionTransportWitnessed ≡ true

open ResponseTransportWitness public

data TransportedResponse
  (source target : PropositionNode)
  (response : ResponseState) : Set where
  transportedWithAllWitnesses :
    ActualResponse source response →
    ResponseTransportWitness source target →
    TransportedResponse source target response

mightConsiderModality : Modality
mightConsiderModality = modality openDeliberation unselected noObligation

commitModality : Modality
commitModality = modality completedDeliberation selected interpersonalCommitment

canonicalMightConsiderNode : PropositionNode
canonicalMightConsiderNode =
  propositionNode
    "might consider bounded help"
    (developmentalCapacityGuard ∷ urgencyGuard ∷ safeRefusalGuard ∷ alternativeAvailableGuard ∷ temporalGuard ∷ [])
    "consider one bounded act of assistance"
    mightConsiderModality
    oneInstanceScope
    0 1 [] ("capacity must still be checked" ∷ []) 0 0

canonicalCommitNode : PropositionNode
canonicalCommitNode =
  propositionNode
    "commit to recurring assistance"
    (safeRefusalGuard ∷ temporalGuard ∷ [])
    "undertake a recurring role"
    commitModality recurringScope 0 100 [] [] 1 1

canonicalMightConsiderResponse : ResponseState
canonicalMightConsiderResponse =
  responseState Trit.pos openZero true true true
    "explicit response to the exact might-consider node"

canonicalMightConsiderActual :
  ActualResponse canonicalMightConsiderNode canonicalMightConsiderResponse
canonicalMightConsiderActual =
  actualResponse true refl true refl true refl refl refl true refl

canonicalMightConsiderBranch : DecisionBranch
canonicalMightConsiderBranch =
  decisionBranch canonicalMightConsiderNode liveContingentBranch openZero 0
    "live in this decision cone; neither guaranteed to be weighed nor selected"

canonicalMightConsiderBranchIsLive :
  branchStatus canonicalMightConsiderBranch ≡ liveContingentBranch
canonicalMightConsiderBranchIsLive = refl

canonicalMightConsiderOptionRemainsOpen :
  branchZeroKind canonicalMightConsiderBranch ≡ openZero
canonicalMightConsiderOptionRemainsOpen = refl

record GuardedResponsePromotionBoundary : Set where
  constructor guardedResponsePromotionBoundary
  field
    flatYesPromotion : Bool
    flatYesPromotionIsFalse : flatYesPromotion ≡ false
    parentToDescendantPromotion : Bool
    parentToDescendantPromotionIsFalse : parentToDescendantPromotion ≡ false
    contextWeakeningPromotion : Bool
    contextWeakeningPromotionIsFalse : contextWeakeningPromotion ≡ false
    considerToCommitPromotion : Bool
    considerToCommitPromotionIsFalse : considerToCommitPromotion ≡ false
    boundedToRecurringPromotion : Bool
    boundedToRecurringPromotionIsFalse : boundedToRecurringPromotion ≡ false
    oldResponseStillValidPromotion : Bool
    oldResponseStillValidPromotionIsFalse : oldResponseStillValidPromotion ≡ false
    expiredMeansRejectedPromotion : Bool
    expiredMeansRejectedPromotionIsFalse : expiredMeansRejectedPromotion ≡ false
    branchMemoryRestoresAuthorityPromotion : Bool
    branchMemoryRestoresAuthorityPromotionIsFalse : branchMemoryRestoresAuthorityPromotion ≡ false
    boundaryReading : String

open GuardedResponsePromotionBoundary public

canonicalGuardedResponsePromotionBoundary : GuardedResponsePromotionBoundary
canonicalGuardedResponsePromotionBoundary =
  guardedResponsePromotionBoundary
    false refl false refl false refl false refl false refl false refl false refl false refl
    "A response binds only the exact proposition node, guards, modality, scope, version, decision token, and time for which a valid witness exists. Affirmation inherits neither downward, outward, upward in modality, nor forward in time by default."

canonicalConsiderToCommitPromotionFalse :
  considerToCommitPromotion canonicalGuardedResponsePromotionBoundary ≡ false
canonicalConsiderToCommitPromotionFalse =
  considerToCommitPromotionIsFalse canonicalGuardedResponsePromotionBoundary
