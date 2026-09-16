module DASHI.ComputerScience.RSA260BidiMksolActionChunkMergeStrengthValidationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.RSA260BidiMksolActionChunkMergeExact as M

strongMergeGateRegression :
  M.MksolActionChunkMergeBoundary.completeChunkRequiresExpectedWorldCount
    M.canonicalMksolActionChunkMergeBoundary
  ≡ true
  × M.MksolActionChunkMergeBoundary.completeChunkRequiresActionOutputRetention
    M.canonicalMksolActionChunkMergeBoundary
  ≡ true
  × M.MksolActionChunkMergeBoundary.completeChunkRequiresR2R10Retention
    M.canonicalMksolActionChunkMergeBoundary
  ≡ true
  × M.MksolActionChunkMergeBoundary.completeChunkRequiresFullRankVectorRetention
    M.canonicalMksolActionChunkMergeBoundary
  ≡ true
strongMergeGateRegression = refl , refl , refl , refl

paymentFirewallRegression :
  M.MksolActionChunkMergeBoundary.completePortfolioReceiptObserved
    M.canonicalMksolActionChunkMergeBoundary
  ≡ false
  × M.MksolActionChunkMergeBoundary.degreeR2R10MergedAdequacyPaid
    M.canonicalMksolActionChunkMergeBoundary
  ≡ false
paymentFirewallRegression = refl , refl
