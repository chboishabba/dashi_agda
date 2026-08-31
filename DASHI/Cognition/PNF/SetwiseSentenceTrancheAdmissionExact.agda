module DASHI.Cognition.PNF.SetwiseSentenceTrancheAdmissionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.IndependentFibreBatchExecutionExact as Batch

------------------------------------------------------------------------
-- E0: sentence closure is semantically independent across sentence fibres.
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

sentenceTrancheExactBatchPreservesAuthority :
  ∀ {Input Authority Receipt : Set}
    (batch : Batch.ExactBatchRealization Input Authority Receipt)
    (input : Input) →
  Batch.batchedAuthority batch input
    ≡ Batch.sequentialAuthority batch input
sentenceTrancheExactBatchPreservesAuthority =
  Batch.batchingPreservesAuthority

------------------------------------------------------------------------
-- E0 scheduler work receipt.
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
-- E0b fixed-family authority admission.
--
-- Once sentence-local semantic deltas have been composed independently, the
-- physical database sink may stage all sentence carriers in tranche-keyed typed
-- relations and merge each authority family once per tranche.  This is stronger
-- than merely sharing a transaction: it excludes recreating staging tables or
-- dispatching the object/factor/demand/export/lookup families once per sentence.
--
-- Exact semantic equality remains owned by SetwiseSentenceTrancheAdmission /
-- ExactBatchRealization above.  This record owns only the physical work shape.
------------------------------------------------------------------------

record FixedFamilySentenceAdmissionReceipt : Set where
  constructor fixedFamilySentenceAdmissionReceipt
  field
    sentenceCount : Nat
    trancheCount : Nat
    typedCopyStreamCount : Nat
    authorityFamilyStatementCount : Nat
    interfaceIdentityQueryCount : Nat
    perSentenceStageCreateCount : Nat
    perSentenceFamilyStatementCount : Nat
    noRequiredPerSentenceStageCreate : perSentenceStageCreateCount ≡ zero
    noRequiredPerSentenceFamilyDispatch : perSentenceFamilyStatementCount ≡ zero

open FixedFamilySentenceAdmissionReceipt public

------------------------------------------------------------------------
-- Workload-geometry admission for process fan-out.
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
singlePartitionUsesSameWorkerKernel = refl

singlePartitionDoesNotRequireProcessPool :
  processPoolRequired canonicalSinglePartitionDirectExecutionStatus
    ≡ false
singlePartitionDoesNotRequireProcessPool = refl

------------------------------------------------------------------------
-- Negative boundaries.
------------------------------------------------------------------------

data SentenceBatchingRequiresIndependentAuthority : Set where
data SentenceBatchingRequiresPerSentenceCommit : Set where
data SentenceBatchingRequiresPerSentenceClaim : Set where
data SentenceBatchingRequiresPerSentenceStageCreate : Set where
data SentenceBatchingRequiresPerSentenceFamilyDispatch : Set where
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

setwiseSentenceBatchingNeedNotCreateStagesPerSentence :
  SentenceBatchingRequiresPerSentenceStageCreate → ⊥
setwiseSentenceBatchingNeedNotCreateStagesPerSentence ()

setwiseSentenceBatchingNeedNotDispatchFamiliesPerSentence :
  SentenceBatchingRequiresPerSentenceFamilyDispatch → ⊥
setwiseSentenceBatchingNeedNotDispatchFamiliesPerSentence ()

singlePartitionNeedNotSpawnProcessPool :
  OnePartitionRequiresProcessPool → ⊥
singlePartitionNeedNotSpawnProcessPool ()
