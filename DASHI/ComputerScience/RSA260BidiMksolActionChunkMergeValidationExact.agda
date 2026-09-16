module DASHI.ComputerScience.RSA260BidiMksolActionChunkMergeValidationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.RSA260BidiMksolActionChunkMergeExact as P

mergeGateRegression :
  P.MksolActionChunkMergeBoundary.fourCompleteChunksRequired
    P.canonicalMksolActionChunkMergeBoundary
  ≡ true
  × P.MksolActionChunkMergeBoundary.mergedExpectedWorldCountIsThirtyFour
    P.canonicalMksolActionChunkMergeBoundary
  ≡ true
  × P.MksolActionChunkMergeBoundary.partialChunkEligibleForCandidateEvaluation
    P.canonicalMksolActionChunkMergeBoundary
  ≡ false
  × P.MksolActionChunkMergeBoundary.completePortfolioReceiptObserved
    P.canonicalMksolActionChunkMergeBoundary
  ≡ false
mergeGateRegression = refl , refl , refl , refl

firewallRegression :
  P.MksolActionChunkMergeBoundary.oeisOverlapCreatesChunkCompletion
    P.canonicalMksolActionChunkMergeBoundary
  ≡ false
  × P.MksolActionChunkMergeBoundary.twelveWorldAdequacyCreatesMergedAdequacy
    P.canonicalMksolActionChunkMergeBoundary
  ≡ false
firewallRegression = refl , refl
