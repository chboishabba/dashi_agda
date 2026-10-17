{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109ResidualInstantiationReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Typed authority receipt for the narrow CMP109 residual-instantiation tranche.
--
-- This is repository-native DASHI bookkeeping.  It records what the tranche
-- establishes and, more importantly, what it does not establish.
------------------------------------------------------------------------

record CMP109ResidualInstantiationReceipt : Set where
  field
    betaDifferenceAlgebraStructurallyPaid : Bool
    betaDifferenceStillNeedsSelectedAttachment : Bool
    generatedHistoryResponseStillNeedsSourceReconstruction : Bool
    physicalCompositeD1StillNeedsTransportEquality : Bool
    genuinelyNewMathematicsEstablished : Bool
    clayPromotion : Bool

------------------------------------------------------------------------

canonicalCMP109ResidualInstantiationReceipt : CMP109ResidualInstantiationReceipt
canonicalCMP109ResidualInstantiationReceipt = record
  { CMP109ResidualInstantiationReceipt.betaDifferenceAlgebraStructurallyPaid = true
  ; CMP109ResidualInstantiationReceipt.betaDifferenceStillNeedsSelectedAttachment = true
  ; CMP109ResidualInstantiationReceipt.generatedHistoryResponseStillNeedsSourceReconstruction = true
  ; CMP109ResidualInstantiationReceipt.physicalCompositeD1StillNeedsTransportEquality = true
  ; CMP109ResidualInstantiationReceipt.genuinelyNewMathematicsEstablished = false
  ; CMP109ResidualInstantiationReceipt.clayPromotion = false
  }

------------------------------------------------------------------------

open CMP109ResidualInstantiationReceipt public

clayPromotionIsFalse :
  clayPromotion canonicalCMP109ResidualInstantiationReceipt ≡ false
clayPromotionIsFalse = refl
