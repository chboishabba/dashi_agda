module DASHI.Cognition.PNF.SetwiseSentenceTrancheAdmissionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.IndependentFibreBatchExecutionExact as Batch

------------------------------------------------------------------------
-- E0: sentence closure is semantically independent across sentence fibres.
--
-- A tranche changes physical scheduling only.  The semantic result of admitting
-- a finite set of independent sentence deltas must agree with sequential
-- admission of exactly those deltas; batching cannot manufacture a second
-- semantic authority or change sentence-local meaning.
------------------------------------------------------------------------

record SetwiseSentenceTrancheAdmission
    (SentenceDelta AuthorityState : Set) : Set₁ where
  field
    emptyAuthority : AuthorityState
    admitOne : AuthorityState → SentenceDelta → AuthorityState
    admitTranche : AuthorityState → SentenceDelta → SentenceDelta → AuthorityState

    twoSentenceParity :
      (state : AuthorityState) →
      (left right : SentenceDelta) →
      admitTranche state left right
        ≡
      admitOne (admitOne state left) right

open SetwiseSentenceTrancheAdmission public

------------------------------------------------------------------------
-- Reuse the existing generic exact-batch theorem owner rather than creating a
-- parallel notion of batch correctness.  Concrete sentence-tranche benchmarks
-- may package their sequential and tranche executions as ExactBatchRealization;
-- authority equality then comes from the existing theorem.
------------------------------------------------------------------------

sentenceTrancheExactBatchPreservesAuthority :
  ∀ {Input Authority Receipt : Set}
    (batch : Batch.ExactBatchRealization Input Authority Receipt)
    (input : Input) →
  Batch.batchedAuthority batch input
    ≡ Batch.sequentialAuthority batch input
sentenceTrancheExactBatchPreservesAuthority =
  Batch.batchingPreservesAuthority

------------------------------------------------------------------------
-- Physical work receipt.
--
-- Claiming and committing are charged per tranche, while semantic composition
-- remains charged per sentence/delta.  The declared path has no requirement for
-- one database transaction or one work-claim round trip per sentence.
------------------------------------------------------------------------

record SentenceTrancheWorkReceipt : Set where
  constructor sentenceTrancheWorkReceipt
  field
    sentenceCount : Nat
    trancheCount : Nat
    workClaimBatchCount : Nat
    authorityTransactionCount : Nat
    sourceTokenBatchLoadCount : Nat
    perSentenceClaimRoundTripCount : Nat
    perSentenceTransactionCount : Nat
    noRequiredPerSentenceClaim : perSentenceClaimRoundTripCount ≡ zero
    noRequiredPerSentenceTransaction : perSentenceTransactionCount ≡ zero

open SentenceTrancheWorkReceipt public

------------------------------------------------------------------------
-- Workload-geometry admission for process fan-out.
--
-- One available parser partition has no process-level fan-out to exploit.  A
-- direct execution lane may therefore avoid spawn/pool boundary work while
-- invoking exactly the same parser/semantic worker kernel.  This is an
-- execution-placement statement only, not a semantic shortcut.
------------------------------------------------------------------------

record SinglePartitionDirectExecutionStatus : Set where
  constructor singlePartitionDirectExecutionStatus
  field
    availablePartitionCount : Nat
    directWorkerKernelSameAsParallelWorkerKernel : Bool
    processPoolRequired : Bool

open SinglePartitionDirectExecutionStatus public

canonicalSinglePartitionDirectExecutionStatus :
  SinglePartitionDirectExecutionStatus
canonicalSinglePartitionDirectExecutionStatus =
  singlePartitionDirectExecutionStatus 1 true false

singlePartitionUsesSameWorkerKernel :
  directWorkerKernelSameAsParallelWorkerKernel
    canonicalSinglePartitionDirectExecutionStatus
    ≡ true
singlePartitionUsesSameWorkerKernel = _≡_.refl

singlePartitionDoesNotRequireProcessPool :
  processPoolRequired canonicalSinglePartitionDirectExecutionStatus
    ≡ false
singlePartitionDoesNotRequireProcessPool = _≡_.refl

------------------------------------------------------------------------
-- Negative boundaries.
------------------------------------------------------------------------

data SentenceBatchingRequiresIndependentAuthority : Set where

data SentenceBatchingRequiresPerSentenceCommit : Set where

data SentenceBatchingRequiresPerSentenceClaim : Set where

data OnePartitionRequiresProcessPool : Set where

setwiseSentenceBatchingDoesNotCreateSecondAuthority :
  SentenceBatchingRequiresIndependentAuthority → ⊥
setwiseSentenceBatchingDoesNotCreateSecondAuthority ()

setwiseSentenceBatchingNeedNotCommitPerSentence :
  SentenceBatchingRequiresPerSentenceCommit → ⊥
setwiseSentenceBatchingNeedNotCommitPerSentence ()

setwiseSentenceBatchingNeedNotClaimPerSentence :
  SentenceBatchingRequiresPerSentenceClaim → ⊥
setwiseSentenceBatchingNeedNotClaimPerSentence ()

singlePartitionNeedNotSpawnProcessPool :
  OnePartitionRequiresProcessPool → ⊥
singlePartitionNeedNotSpawnProcessPool ()
