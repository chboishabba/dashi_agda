{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ResidualContractionReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Typed DASHI authority receipt for the CMP116 R409/R429 contraction tranche.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- The distinctions below are DASHI bookkeeping/extension claims.  They do not
-- attribute the repository's compiler decomposition or authority semantics to
-- Bałaban, and they do not create any Clay theorem inhabitant.
------------------------------------------------------------------------

record CMP116ResidualContractionReceipt : Set where
  field
    r409ReplayReceiptsAreProofAuthority : Bool
    r409SelectedProofEqualityStillRequired : Bool
    r429CompilerStructurePaysQuantitativeBound : Bool
    r429QuantitativeBoundStillRequired : Bool
    r429SameObjectTraceAttachmentStillRequired : Bool
    clayPromotion : Bool

------------------------------------------------------------------------

canonicalCMP116ResidualContractionReceipt : CMP116ResidualContractionReceipt
canonicalCMP116ResidualContractionReceipt = record
  { CMP116ResidualContractionReceipt.r409ReplayReceiptsAreProofAuthority = false
  ; CMP116ResidualContractionReceipt.r409SelectedProofEqualityStillRequired = true
  ; CMP116ResidualContractionReceipt.r429CompilerStructurePaysQuantitativeBound = false
  ; CMP116ResidualContractionReceipt.r429QuantitativeBoundStillRequired = true
  ; CMP116ResidualContractionReceipt.r429SameObjectTraceAttachmentStillRequired = true
  ; CMP116ResidualContractionReceipt.clayPromotion = false
  }

------------------------------------------------------------------------

open CMP116ResidualContractionReceipt public

clayPromotionIsFalse :
  clayPromotion canonicalCMP116ResidualContractionReceipt ≡ false
clayPromotionIsFalse = refl
