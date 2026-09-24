{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTPostMergeMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.GRQFTPostMergeMaxCutExact as M

cmp119SectorCompilerClosed :
  M.cmp119ToSelectedSharedSectorCompilerClosed
    M.canonicalGRQFTPostMergeMaxCut
  ≡ true
cmp119SectorCompilerClosed = refl

activeSectorTotalizationStillOpen :
  M.activePhysicalSectorTotalizationStillRequired
    M.canonicalGRQFTPostMergeMaxCut
  ≡ true
allSectorAggregationStillOpen = refl

terminalStillFalse :
  M.terminalGRQFTPromoted M.canonicalGRQFTPostMergeMaxCut ≡ false
terminalStillFalse = refl
