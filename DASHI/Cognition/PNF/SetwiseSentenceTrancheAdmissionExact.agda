module DASHI.Cognition.PNF.SetwiseSentenceTrancheAdmissionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

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
-- Negative boundaries.
------------------------------------------------------------------------

data SentenceBatchingRequiresIndependentAuthority : Set where

data SentenceBatchingRequiresPerSentenceCommit : Set where

data SentenceBatchingRequiresPerSentenceClaim : Set where

setwiseSentenceBatchingDoesNotCreateSecondAuthority :
  SentenceBatchingRequiresIndependentAuthority → ⊥
setwiseSentenceBatchingDoesNotCreateSecondAuthority ()

setwiseSentenceBatchingNeedNotCommitPerSentence :
  SentenceBatchingRequiresPerSentenceCommit → ⊥
setwiseSentenceBatchingNeedNotCommitPerSentence ()

setwiseSentenceBatchingNeedNotClaimPerSentence :
  SentenceBatchingRequiresPerSentenceClaim → ⊥
setwiseSentenceBatchingNeedNotClaimPerSentence ()
