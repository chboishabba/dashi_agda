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
-- all four declared chunks are complete.  It does not invent any runtime data.
------------------------------------------------------------------------

record CompleteActionStressChunks : Set where
  constructor complete-action-stress-chunks
  field
    chunk00to07 : Stress.ChunkExecutionReceipt
    chunk08to15 : Stress.ChunkExecutionReceipt
    chunk16to23 : Stress.ChunkExecutionReceipt
    chunk24to33 : Stress.ChunkExecutionReceipt

    chunk00to07Complete : Stress.complete chunk00to07 ≡ true
    chunk08to15Complete : Stress.complete chunk08to15 ≡ true
    chunk16to23Complete : Stress.complete chunk16to23 ≡ true
    chunk24to33Complete : Stress.complete chunk24to33 ≡ true
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

partialChunkDoesNotPermitEvaluation :
  PartialChunkEligibleForCandidateEvaluation -> ⊥
partialChunkDoesNotPermitEvaluation ()

oeisDoesNotCreateChunkCompletion : OEISOverlapCreatesChunkCompletion -> ⊥
oeisDoesNotCreateChunkCompletion ()

twelveWorldAdequacyDoesNotCreateMergedAdequacy :
  TwelveWorldAdequacyCreatesMergedAdequacy -> ⊥
twelveWorldAdequacyDoesNotCreateMergedAdequacy ()

record MksolActionChunkMergeBoundary : Set where
  constructor mksol-action-chunk-merge-boundary
  field
    fourCompleteChunksRequired : Bool
    mergedExpectedWorldCountIsThirtyFour : Bool
    partialChunkEligibleForCandidateEvaluation : Bool
    completePortfolioReceiptObserved : Bool
    degreeR2R10MergedAdequacyPaid : Bool
    oeisOverlapCreatesChunkCompletion : Bool
    twelveWorldAdequacyCreatesMergedAdequacy : Bool
open MksolActionChunkMergeBoundary public

canonicalMksolActionChunkMergeBoundary : MksolActionChunkMergeBoundary
canonicalMksolActionChunkMergeBoundary =
  mksol-action-chunk-merge-boundary
    true true false false false false false
