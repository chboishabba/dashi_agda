{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119PinnedYMGRQFTSectorStressBridgeValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119PinnedYMGRQFTSectorStressBridgeExact as B

noThirdStressTheorem :
  B.secondCMP119ToSharedStressTheoremRequired ≡ false
noThirdStressTheorem = refl
