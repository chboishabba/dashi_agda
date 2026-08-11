module DASHI.Cognition.PNF.AdjacentReconciliationWork where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.NumericAuthority
open import DASHI.Cognition.PNF.NumericHyperfabric

------------------------------------------------------------------------
-- Adjacent regions are overlapping execution fibres. They do not replace the
-- canonical containment parent and adjacency alone proves no semantic relation.
------------------------------------------------------------------------

data AdjacentScale : Set where
  adjacentSentenceScale adjacentParagraphScale : AdjacentScale

data LocalClosure : Set where
  memberLocallyClosed : LocalClosure

record AdjacentMember : Set where
  constructor adjacentMember
  field
    memberRegion : RegionId
    canonicalParent : RegionId
    memberStart memberEnd : Nat
    memberClosure : LocalClosure

open AdjacentMember public

record OrderedAdjacentPair : Set where
  constructor orderedAdjacentPair
  field
    pairScale : AdjacentScale
    leftMember rightMember : AdjacentMember
    sharedCanonicalParent :
      canonicalParent leftMember ≡ canonicalParent rightMember
    leftDoesNotOverlapRight :
      memberEnd leftMember ≤ᶜ memberStart rightMember

open OrderedAdjacentPair public

data ReconciliationWorkState : Set where
  reconciliationReady reconciliationLeased : ReconciliationWorkState
  reconciliationCompleted reconciliationFailed : ReconciliationWorkState

record AdjacentWorkItem : Set where
  constructor adjacentWorkItem
  field
    pairRegion : RegionId
    pair : OrderedAdjacentPair
    state : ReconciliationWorkState
    leaseEpoch : Nat

open AdjacentWorkItem public

materializeAdjacentWork : RegionId → OrderedAdjacentPair → AdjacentWorkItem
materializeAdjacentWork region pair =
  adjacentWorkItem region pair reconciliationReady zero

------------------------------------------------------------------------
-- No target is resolved merely because two closed siblings are adjacent.
------------------------------------------------------------------------

data ResolutionEvidence : Set where
  checkedCandidateRelation : ResolutionEvidence

data ResolutionDecision : Set where
  unresolvedAtAdjacentBoundary : ResolutionDecision
  resolvedWithEvidence : ResolutionEvidence → ResolutionDecision

adjacencyAloneDoesNotResolve : ResolutionDecision
adjacencyAloneDoesNotResolve = unresolvedAtAdjacentBoundary

resolveAdjacentDemand : ResolutionEvidence → ResolutionDecision
resolveAdjacentDemand = resolvedWithEvidence

unresolvedIsNotCheckedResolution :
  unresolvedAtAdjacentBoundary ≡
    resolvedWithEvidence checkedCandidateRelation → ⊥
unresolvedIsNotCheckedResolution ()

------------------------------------------------------------------------
-- A linear sibling sequence has at most one immediate pair per boundary.
------------------------------------------------------------------------

adjacentPairCapacity : Nat → Nat
adjacentPairCapacity zero = zero
adjacentPairCapacity (suc zero) = zero
adjacentPairCapacity (suc (suc n)) = suc n

adjacentPairCapacityTwo : adjacentPairCapacity (suc (suc zero)) ≡ suc zero
adjacentPairCapacityTwo = refl

record AdjacentExecutionStatus : Set where
  constructor adjacentExecutionStatus
  field
    pairCarrierMaterialized : Bool
    durableWorkQueued : Bool
    fencedExecutorAvailable : Bool
    sentencePairDrainWired : Bool
    paragraphPairDrainWired : Bool
    checkedCandidatesStoredSeparately : Bool
    adjacencyAutoResolvesDemands : Bool

open AdjacentExecutionStatus public

currentPR470AdjacentStatus : AdjacentExecutionStatus
currentPR470AdjacentStatus =
  adjacentExecutionStatus true true true true true true false

record AdjacentAuthorityBoundary : Set where
  constructor adjacentAuthorityBoundary
  field
    carrierMaterializationIsWired :
      pairCarrierMaterialized currentPR470AdjacentStatus ≡ true
    fencedExecutorIsWired :
      fencedExecutorAvailable currentPR470AdjacentStatus ≡ true
    sentenceDrainIsWired :
      sentencePairDrainWired currentPR470AdjacentStatus ≡ true
    paragraphDrainIsWired :
      paragraphPairDrainWired currentPR470AdjacentStatus ≡ true
    candidateEvidenceRemainsSeparate :
      checkedCandidatesStoredSeparately currentPR470AdjacentStatus ≡ true
    adjacencyDoesNotAutoResolve :
      adjacencyAutoResolvesDemands currentPR470AdjacentStatus ≡ false

canonicalAdjacentAuthorityBoundary : AdjacentAuthorityBoundary
canonicalAdjacentAuthorityBoundary =
  adjacentAuthorityBoundary refl refl refl refl refl refl
