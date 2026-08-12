module DASHI.Cognition.PNF.BoundedExecutionCarrier where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; length)

open import DASHI.Cognition.PNF.ComplexityArithmetic
import DASHI.Cognition.PNF.BoundedProperNameEvidenceExecution as ProperName
import DASHI.Cognition.PNF.BoundedFactorCompositionExecution as Composition
import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance

------------------------------------------------------------------------
-- Generic bounded-execution carrier.
------------------------------------------------------------------------

record BoundedEnumeration : Set where
  constructor boundedEnumeration
  field
    possibleCount : Nat
    retainedCount : Nat
    retainedLimit : Nat
    retainedWithinLimit : retainedCount ≤ᶜ retainedLimit

open BoundedEnumeration public

data EnumerationCoverage : Set where
  completeEnumeration boundedRepresentativeEnumeration : EnumerationCoverage

record BoundedExecutionCarrier (Candidate : Set) : Set where
  constructor boundedExecutionCarrier
  field
    enumeration : BoundedEnumeration
    retainedCandidates : List Candidate
    retainedCountMatches :
      length retainedCandidates ≡ retainedCount enumeration
    coverage : EnumerationCoverage

open BoundedExecutionCarrier public

record GenericOverflowReceipt : Set where
  constructor genericOverflowReceipt
  field
    overflowEnumeration : BoundedEnumeration
    overflowCoverage : EnumerationCoverage

open GenericOverflowReceipt public

data OverflowSemanticAuthority : Set where
  executionEvidenceOnly : OverflowSemanticAuthority

data OverflowSemanticPermission : OverflowSemanticAuthority → Set where

executionOverflowHasNoSemanticPermission :
  OverflowSemanticPermission executionEvidenceOnly → ⊥
executionOverflowHasNoSemanticPermission ()

------------------------------------------------------------------------
-- Optional measure/mass receipt.
--
-- This legacy two-way receipt remains useful when the represented universe is
-- closed for a particular calculation.  Consumer-indexed/open-world accounting
-- is provided below without changing existing callers.
------------------------------------------------------------------------

record SplitMeasureReceipt
    (Mass : Set)
    (_⊕_ : Mass → Mass → Mass) : Set where
  constructor splitMeasureReceipt
  field
    totalMass retainedMass omittedMass : Mass
    retainedPlusOmittedIsTotal :
      retainedMass ⊕ omittedMass ≡ totalMass

open SplitMeasureReceipt public

record MeasuredBoundedExecutionCarrier
    (Candidate Mass : Set)
    (_⊕_ : Mass → Mass → Mass) : Set where
  constructor measuredBoundedExecutionCarrier
  field
    boundedCarrier : BoundedExecutionCarrier Candidate
    measureReceipt : SplitMeasureReceipt Mass _⊕_

open MeasuredBoundedExecutionCarrier public

------------------------------------------------------------------------
-- Explicit semantic P/Q execution partition.
--
-- This strengthens the count-only carrier for search/beam implementations.
-- P is the currently active execution surface; Q is the residual semantic
-- region.  Q remains semantically possible and carries a reopening receipt.
-- Refutation is deliberately absent from this type.
------------------------------------------------------------------------

record ReopenableExecutionPartition (Candidate : Set) : Set₁ where
  constructor reopenableExecutionPartition
  field
    activeCarrier : BoundedExecutionCarrier Candidate
    SemanticallyPossible : Candidate → Set
    Active : Candidate → Set
    Residual : Candidate → Set
    activeImpliesPossible :
      ∀ {candidate} → Active candidate → SemanticallyPossible candidate
    residualImpliesPossible :
      ∀ {candidate} → Residual candidate → SemanticallyPossible candidate
    activeResidualDisjoint :
      ∀ {candidate} → Active candidate → Residual candidate → ⊥
    ReopenReceipt : Set
    residualReceipt :
      ∀ {candidate} → Residual candidate → ReopenReceipt

open ReopenableExecutionPartition public

record MeasuredReopenableExecutionPartition
    (Candidate Mass : Set)
    (_⊕_ : Mass → Mass → Mass) : Set₁ where
  constructor measuredReopenableExecutionPartition
  field
    partition : ReopenableExecutionPartition Candidate
    massReceipt : SplitMeasureReceipt Mass _⊕_

open MeasuredReopenableExecutionPartition public

------------------------------------------------------------------------
-- Consumer-indexed/open-world mass accounting for bounded execution.
--
-- This is the runtime form of "active beam P + semantic residual Q + explicit
-- outside-model ignorance".  The region interpretation is application-supplied
-- so candidate sets, provenance distinctions, or task-relevance regions can all
-- instantiate the same carrier without pretending they are probabilities.
------------------------------------------------------------------------

record ConsumerMeasuredReopenableExecutionPartition
    (Candidate Consumer Region Mass : Set) : Set₁ where
  constructor consumerMeasuredReopenableExecutionPartition
  field
    partition : ReopenableExecutionPartition Candidate
    relevanceMeasure :
      Relevance.ConsumerIndexedRelevanceMeasure Consumer Region Mass
    consumer : Consumer
    openWorldAccounting :
      Relevance.OpenWorldMassAccounting relevanceMeasure consumer

open ConsumerMeasuredReopenableExecutionPartition public

data ResidualSemanticRejectionPermission : Set where

residualExecutionStateCannotRejectSemantics :
  ResidualSemanticRejectionPermission → ⊥
residualExecutionStateCannotRejectSemantics ()

------------------------------------------------------------------------
-- Existing runtime-specific bounded carriers embed into the generic shape.
------------------------------------------------------------------------

properNameEnumerationAsGeneric :
  ProperName.ProperNameTargetEnumeration → BoundedEnumeration
properNameEnumerationAsGeneric e =
  boundedEnumeration
    (ProperName.possibleTargetCount e)
    (ProperName.retainedTargetCount e)
    (ProperName.retainedTargetLimit e)
    (ProperName.retainedWithinLimit e)

compositionEnumerationAsGeneric :
  Composition.CompositionEnumeration → BoundedEnumeration
compositionEnumerationAsGeneric e =
  boundedEnumeration
    (Composition.possiblePairCount e)
    (Composition.retainedPairCount e)
    (Composition.retainedPairLimit e)
    (Composition.retainedWithinLimit e)

record BoundedExecutionAuthorityBoundary : Set where
  constructor boundedExecutionAuthorityBoundary
  field
    overflowCannotPromoteSemantics :
      OverflowSemanticPermission executionEvidenceOnly → ⊥
    residualCannotBecomeSemanticRejection :
      ResidualSemanticRejectionPermission → ⊥

open BoundedExecutionAuthorityBoundary public

canonicalBoundedExecutionAuthorityBoundary : BoundedExecutionAuthorityBoundary
canonicalBoundedExecutionAuthorityBoundary =
  boundedExecutionAuthorityBoundary
    executionOverflowHasNoSemanticPermission
    residualExecutionStateCannotRejectSemantics
