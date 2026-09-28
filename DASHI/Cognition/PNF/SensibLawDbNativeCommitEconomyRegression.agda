{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.SensibLawDbNativeCommitEconomyRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([]; _∷_)

import DASHI.Cognition.PNF.IndependentFibreBatchExecutionExact as Batch
import DASHI.Cognition.PNF.SensibLawDbNativeCommitEconomyExact as Economy

data FixtureInput : Set where
  fixtureInput : FixtureInput

data FixtureAuthority : Set where
  fixtureAuthority : FixtureAuthority

fixtureWrite : Economy.DurableWrite
fixtureWrite =
  Economy.durable-write
    "write:fixture"
    "semantic-product:fixture"
    "occurrence-binding:fixture"
    true refl
    false refl
    false refl
    false refl

fixtureReceipt : Economy.DurableExecutionReceipt
fixtureReceipt =
  Economy.durable-execution-receipt
    "durable-execution:fixture"
    (fixtureWrite ∷ [])
    1
    true refl
    true refl
    false refl
    false refl
    false refl

fixtureSemanticBatch :
  Batch.ExactBatchRealization
    FixtureInput
    FixtureAuthority
    Economy.DurableExecutionReceipt
fixtureSemanticBatch = record
  { Batch.sequentialAuthority = λ _ → fixtureAuthority
  ; Batch.batchedAuthority = λ _ → fixtureAuthority
  ; Batch.batchExact = λ _ → refl
  ; Batch.receipt = λ _ → fixtureReceipt
  }

fixtureExactDurableBatch :
  Economy.ExactDurableBatchRealization FixtureInput FixtureAuthority
fixtureExactDurableBatch =
  Economy.exact-durable-batch-realization
    fixtureSemanticBatch
    (λ _ → 10)
    (λ _ → 1)
    (λ _ → true)
    (λ _ → refl)

fixtureBatchedAuthorityMatchesSequential :
  Batch.batchedAuthority
    (Economy.semanticBatch fixtureExactDurableBatch)
    fixtureInput
  ≡
  Batch.sequentialAuthority
    (Economy.semanticBatch fixtureExactDurableBatch)
    fixtureInput
fixtureBatchedAuthorityMatchesSequential =
  Economy.batchedDurabilityPreservesAuthority
    fixtureExactDurableBatch
    fixtureInput

fixtureCommitCoalescingStaysCandidateOnly :
  Economy.DurableWrite.candidateOnly fixtureWrite ≡ true
fixtureCommitCoalescingStaysCandidateOnly = refl

fixtureCommitCoalescingDoesNotCreateAuthority :
  Economy.DurableWrite.createsSemanticAuthority fixtureWrite ≡ false
fixtureCommitCoalescingDoesNotCreateAuthority = refl

fixtureReceiptReopensExactly :
  Economy.DurableExecutionReceipt.exactReopenValidated fixtureReceipt ≡ true
fixtureReceiptReopensExactly = refl
