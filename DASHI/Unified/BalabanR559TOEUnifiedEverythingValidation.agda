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
