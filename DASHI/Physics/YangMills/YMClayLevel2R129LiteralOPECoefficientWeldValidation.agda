{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2R129LiteralOPECoefficientWeldValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2R129LiteralOPECoefficientWeldExact as D2

noParallelCompositeTheory :
  D2.parallelCompositeOperatorTheoryAllowedByD2 ≡ false
noParallelCompositeTheory = refl

sameFamilyAttachmentStillPhysical :
  D2.r129SameFamilyOperatorAttachmentStillPhysical ≡ true
sameFamilyAttachmentStillPhysical = refl

promotionFailClosed :
  D2.clayPromotion ≡ false
promotionFailClosed = refl
