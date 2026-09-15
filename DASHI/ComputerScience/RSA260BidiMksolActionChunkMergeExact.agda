module DASHI.ComputerScience.RSA260BidiMksolActionChunkMergeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiMksolActionChunkedStressExact as Stress

------------------------------------------------------------------------
-- COMPLETE-CHUNK MERGE GATE
--
-- The wider action-consumer stress is intentionally chunked.  This owner makes
-- the promotion boundary explicit: candidate evaluation is permitted only once
-- all four declared chunks are complete and internally coherent.  A Boolean
-- `complete` flag is not by itself a receipt: the observed world count must
-- equal the declared chunk size, and all consumer-relevant outputs/coordinates
-- must have been retained.
------------------------------------------------------------------------

record VerifiedChunkReceipt (expected : Stress.ActionStressChunk) : Set where
  constructor verified-chunk-receipt
  field
    receipt : Stress.ChunkExecutionReceipt
    chunkMatchesExpected : Stress.chunk receipt ≡ expected
    completedCountMatchesExpected :
      Stress.completedWorldCount receipt ≡ Stress.chunkExpectedWorldCount expected
    completeIsTrue : Stress.complete receipt ≡ true
    actionOutputsRetainedIsTrue : Stress.actionOutputsRetained receipt ≡ true
    rankR2RetainedIsTrue : Stress.rankR2Retained receipt ≡ true
    rankR10RetainedIsTrue : Stress.rankR10Retained receipt ≡ true
    allRanksRetainedIsTrue :
      Stress.allUniversallyAvailableRankCoordinatesRetained receipt ≡ true
open VerifiedChunkReceipt public

record CompleteActionStressChunks : Set where
  constructor complete-action-stress-chunks
  field
    chunk00to07 : VerifiedChunkReceipt Stress.worlds00to07
    chunk08to15 : VerifiedChunkReceipt Stress.worlds08to15
    chunk16to23 : VerifiedChunkReceipt Stress.worlds16to23
    chunk24to33 : VerifiedChunkReceipt Stress.worlds24to33
open CompleteActionStressChunks public

mergedExpectedWorldCount : Nat
mergedExpectedWorldCount =
  Stress.chunkExpectedWorldCount Stress.worlds00to07
  + Stress.chunkExpectedWorldCount Stress.worlds08to15
  + Stress.chunkExpectedWorldCount Stress.worlds16to23
  + Stress.chunkExpectedWorldCount Stress.worlds24to33

mergedExpectedWorldCountIsThirtyFour : mergedExpectedWorldCount ≡ 34
mergedExpectedWorldCountIsThirtyFour = refl

------------------------------------------------------------------------
-- WrongType / receipt firewalls.
------------------------------------------------------------------------

data PartialChunkEligibleForCandidateEvaluation : Set where
data OEISOverlapCreatesChunkCompletion : Set where
data TwelveWorldAdequacyCreatesMergedAdequacy : Set where
data CompletionFlagAloneCreatesVerifiedChunk : Set where

partialChunkDoesNotPermitEvaluation :
  PartialChunkEligibleForCandidateEvaluation -> ⊥
partialChunkDoesNotPermitEvaluation ()

oeisDoesNotCreateChunkCompletion : OEISOverlapCreatesChunkCompletion -> ⊥
oeisDoesNotCreateChunkCompletion ()

twelveWorldAdequacyDoesNotCreateMergedAdequacy :
  TwelveWorldAdequacyCreatesMergedAdequacy -> ⊥
twelveWorldAdequacyDoesNotCreateMergedAdequacy ()

completionFlagAloneDoesNotCreateVerifiedChunk :
  CompletionFlagAloneCreatesVerifiedChunk -> ⊥
completionFlagAloneDoesNotCreateVerifiedChunk ()

record MksolActionChunkMergeBoundary : Set where
  constructor mksol-action-chunk-merge-boundary
  field
    fourCompleteChunksRequired : Bool
    mergedExpectedWorldCountIsThirtyFour : Bool
    completeChunkRequiresExpectedWorldCount : Bool
    completeChunkRequiresActionOutputRetention : Bool
    completeChunkRequiresR2R10Retention : Bool
    completeChunkRequiresFullRankVectorRetention : Bool
    completionFlagAloneCreatesVerifiedChunk : Bool
    partialChunkEligibleForCandidateEvaluation : Bool
    completePortfolioReceiptObserved : Bool
    degreeR2R10MergedAdequacyPaid : Bool
    oeisOverlapCreatesChunkCompletion : Bool
    twelveWorldAdequacyCreatesMergedAdequacy : Bool
open MksolActionChunkMergeBoundary public

canonicalMksolActionChunkMergeBoundary : MksolActionChunkMergeBoundary
canonicalMksolActionChunkMergeBoundary =
  mksol-action-chunk-merge-boundary
    true true
    true true true true
    false false
    false false
    false false
