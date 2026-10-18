{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.SensibLawDbNativeCommitEconomyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.EditTransportLeafLocalityExact as Locality
import DASHI.Cognition.PNF.IndependentFibreBatchExecutionExact as Batch

------------------------------------------------------------------------
-- SCALE-1.P durable commit economy.
--
-- This owner is deliberately physical, not semantic.
--
-- The locality owners answer:
--   "which source/semantic products are invalidated by this edit?"
--
-- The durable execution owner answers:
--   "given the same declared semantic writes, can we realize them with fewer
--    durable commit barriers while preserving the exact authority result?"
--
-- PostgreSQL COMMIT/fsync/ZIL latency is therefore an execution-cost concern.
-- It must not be retyped as parser work, semantic recomputation, review,
-- admission, or truth.
------------------------------------------------------------------------

record DurableWrite : Set where
  constructor durable-write
  field
    writeRef : String
    semanticProductRef : String
    occurrenceBindingRef : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open DurableWrite public

record DurableExecutionReceipt : Set where
  constructor durable-execution-receipt
  field
    executionRef : String
    writes : List DurableWrite
    durableCommitBarrierCount : Nat

    allWritesPersisted : Bool
    allWritesPersistedIsTrue :
      allWritesPersisted ≡ true

    exactReopenValidated : Bool
    exactReopenValidatedIsTrue :
      exactReopenValidated ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open DurableExecutionReceipt public

------------------------------------------------------------------------
-- Exact batching contract.
--
-- The caller supplies the semantic authority carrier.  Sequential and batched
-- durable executions are acceptable only when their authority results are
-- definitionally/equationally the same.  The receipt may additionally record
-- that the physical implementation reduced commit barriers; that fact is not
-- itself a semantic proof.
------------------------------------------------------------------------

record ExactDurableBatchRealization
    (Input Authority : Set) : Set₁ where
  constructor exact-durable-batch-realization
  field
    semanticBatch : Batch.ExactBatchRealization
      Input Authority DurableExecutionReceipt

    sequentialCommitBarrierCount : Input → Nat
    batchedCommitBarrierCount : Input → Nat

    fewerDurableCommitBarriers : Input → Bool
    fewerDurableCommitBarriersIsTrue :
      (input : Input) → fewerDurableCommitBarriers input ≡ true

open ExactDurableBatchRealization public

batchedDurabilityPreservesAuthority :
  {Input Authority : Set} →
  (realization : ExactDurableBatchRealization Input Authority) →
  (input : Input) →
  Batch.batchedAuthority (semanticBatch realization) input
    ≡ Batch.sequentialAuthority (semanticBatch realization) input
batchedDurabilityPreservesAuthority realization =
  Batch.batchingPreservesAuthority (semanticBatch realization)

------------------------------------------------------------------------
-- Locality / physical-economy non-collapse.
------------------------------------------------------------------------

data VerifiedLocalityImpliesFewCommitBarriers : Set where
data FewCommitBarriersProveSemanticIndependence : Set where
data CommitCoalescingCreatesSemanticAdmission : Set where
data CommitCoalescingCreatesSemanticAuthority : Set where
data CommitCoalescingCreatesApplicability : Set where
data CommitCoalescingCreatesClaimTruth : Set where
data StorageSyncLatencyIsSemanticRecomputation : Set where

verifiedLocalityDoesNotImplyFewCommitBarriers :
  VerifiedLocalityImpliesFewCommitBarriers → ⊥
verifiedLocalityDoesNotImplyFewCommitBarriers ()

fewCommitBarriersDoNotProveSemanticIndependence :
  FewCommitBarriersProveSemanticIndependence → ⊥
fewCommitBarriersDoNotProveSemanticIndependence ()

commitCoalescingDoesNotCreateSemanticAdmission :
  CommitCoalescingCreatesSemanticAdmission → ⊥
commitCoalescingDoesNotCreateSemanticAdmission ()

commitCoalescingDoesNotCreateSemanticAuthority :
  CommitCoalescingCreatesSemanticAuthority → ⊥
commitCoalescingDoesNotCreateSemanticAuthority ()

commitCoalescingDoesNotCreateApplicability :
  CommitCoalescingCreatesApplicability → ⊥
commitCoalescingDoesNotCreateApplicability ()

commitCoalescingDoesNotCreateClaimTruth :
  CommitCoalescingCreatesClaimTruth → ⊥
commitCoalescingDoesNotCreateClaimTruth ()

storageSyncLatencyDoesNotBecomeSemanticRecomputation :
  StorageSyncLatencyIsSemanticRecomputation → ⊥
storageSyncLatencyDoesNotBecomeSemanticRecomputation ()

------------------------------------------------------------------------
-- Connection to edit-locality certificates.
--
-- A locality certificate may bound the semantic writes that are necessary,
-- but it deliberately says nothing about how many COMMIT/fsync barriers a
-- physical database realization must use for those writes.
------------------------------------------------------------------------

record LocalityBoundedDurableExecution
    {Before After SourceAtom : Set}
    (Eligible : Before → Set)
    (Match : Before → After → Set)
    (closure : Locality.EditedDependencyClosure SourceAtom After)
    (Changed : After → Set) : Set₁ where
  constructor locality-bounded-durable-execution
  field
    locality :
      Locality.VerifiedEditLocality Eligible Match closure Changed

    durableReceipt : DurableExecutionReceipt

    localityDeterminesCommitBarrierCount : Bool
    localityDeterminesCommitBarrierCountIsFalse :
      localityDeterminesCommitBarrierCount ≡ false

open LocalityBoundedDurableExecution public
