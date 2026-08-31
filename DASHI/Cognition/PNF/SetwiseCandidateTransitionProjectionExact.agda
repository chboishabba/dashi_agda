module DASHI.Cognition.PNF.SetwiseCandidateTransitionProjectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic

------------------------------------------------------------------------
-- Set-wise execution projection.
--
-- Candidate planning history is append-only authority.  Replacing a row-level
-- trigger implementation by one transition-table statement is admissible only
-- when it preserves the same authoritative observations/events and produces the
-- same rebuildable current-state projection.
------------------------------------------------------------------------

record CandidateTransitionBatch : Set where
  constructor candidateTransitionBatch
  field
    insertedCandidates : Nat
    deletedCandidates : Nat
    candidateTransitions : Nat
    transitionCountExact :
      candidateTransitions ≡ insertedCandidates + deletedCandidates

    observationRows : Nat
    executionEventRows : Nat
    observationAuthorityExact : observationRows ≡ candidateTransitions
    executionHistoryExact : executionEventRows ≡ candidateTransitions

    currentProjectionWrites : Nat
    currentProjectionBound : currentProjectionWrites ≤ᶜ candidateTransitions

    candidateMutationStatements : Nat
    eventProjectionStatements : Nat
    statementTriggerInvocations : Nat
    statementTriggerCountExact :
      statementTriggerInvocations ≡
        candidateMutationStatements + eventProjectionStatements

open CandidateTransitionBatch public

------------------------------------------------------------------------
-- Semantic equivalence is stated independently of trigger mechanics.
------------------------------------------------------------------------

record SetwiseProjectionEquivalence
    (AuthorityHistory CurrentProjection : Set) : Set₁ where
  constructor setwiseProjectionEquivalence
  field
    rowwiseAuthorityHistory : AuthorityHistory
    setwiseAuthorityHistory : AuthorityHistory
    authorityHistoryPreserved :
      setwiseAuthorityHistory ≡ rowwiseAuthorityHistory

    rowwiseCurrentProjection : CurrentProjection
    setwiseCurrentProjection : CurrentProjection
    currentProjectionPreserved :
      setwiseCurrentProjection ≡ rowwiseCurrentProjection

open SetwiseProjectionEquivalence public

------------------------------------------------------------------------
-- Runtime correspondence: batching is an execution transformation, not a
-- semantic-history compression theorem.  A future planner may reduce redundant
-- transitions only under a separate semantic equivalence argument.
------------------------------------------------------------------------

record CandidateBatchRuntimeBoundary : Set where
  constructor candidateBatchRuntimeBoundary
  field
    batch : CandidateTransitionBatch
    candidateHistoryIsAuthority : SetwiseProjectionEquivalence Nat Nat

open CandidateBatchRuntimeBoundary public

data BatchProjectionMayDropAuthorityHistory : Set where

data BatchProjectionMayChangeCurrentMeaning : Set where

data BatchImpliesPlannerTransitionElision : Set where

batchMustPreserveAuthorityHistory : BatchProjectionMayDropAuthorityHistory → ⊥
batchMustPreserveAuthorityHistory ()

batchMustPreserveCurrentMeaning : BatchProjectionMayChangeCurrentMeaning → ⊥
batchMustPreserveCurrentMeaning ()

batchingDoesNotProveTransitionElision : BatchImpliesPlannerTransitionElision → ⊥
batchingDoesNotProveTransitionElision ()
