{-# OPTIONS --safe #-}
module DASHI.Unified.BalabanR559TOEUnifiedEverythingValidation where

------------------------------------------------------------------------
-- TERMINAL AGGREGATE VALIDATION.
--
-- This module is intentionally not imported by DASHI.Unified.Everything.
-- The focused workflow checks it after the aggregate has been constructed.
-- This keeps the import graph acyclic.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
open import Data.Empty using (⊥)

import DASHI.Unified.BalabanR559TOEMaxCutExact as Joint
import DASHI.Unified.Everything as UnifiedEverything

unifiedEverythingReceiptMatches :
  UnifiedEverything.unifiedBalabanR559MaxCutReceipt
  ≡ Joint.canonicalBalabanR559TOEMaxCutReceipt
unifiedEverythingReceiptMatches = refl

unifiedEverythingScaleTransferPromotionEliminates :
  Joint.ScaleTransferPromotion → ⊥
unifiedEverythingScaleTransferPromotionEliminates =
  UnifiedEverything.unifiedBalabanScaleTransferNonPromotion


------------------------------------------------------------------------
-- Canonical 58-gap Gate-4 reachability through the terminal aggregate.
------------------------------------------------------------------------

unifiedEverythingGate4CountIs58 :
  UnifiedEverything.unifiedBalabanR559Gate4UnresolvedCount ≡ 58
unifiedEverythingGate4CountIs58 =
  UnifiedEverything.unifiedBalabanR559Gate4UnresolvedCountIs58

unifiedEverythingGate4DefinitionLevelMatches :
  UnifiedEverything.unifiedBalabanR559Gate4DefinitionLevel
  ≡ Joint.gate4DefinitionLevel Joint.canonicalBalabanR559TOEMaxCutReceipt
unifiedEverythingGate4DefinitionLevelMatches = refl

unifiedEverythingGate4InhabitantsLevelMatches :
  UnifiedEverything.unifiedBalabanR559Gate4InhabitantsLevel
  ≡ Joint.gate4InhabitantsLevel Joint.canonicalBalabanR559TOEMaxCutReceipt
unifiedEverythingGate4InhabitantsLevelMatches = refl
