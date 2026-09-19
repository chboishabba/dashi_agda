{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonS2QuantitativeBoundAttachmentValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayLiteralWilsonS2QuantitativeBoundAttachmentExact as S2Q

------------------------------------------------------------------------
-- Regression: the concrete rational-SU(2) finite-product bound compiler means
-- S2 no longer needs three independent boundedness leaves.  The shortest
-- physical interface keeps only the quantitative-bound -> T5-predicate
-- attachment, plus the genuine same-algebra and support/time coordinates.
------------------------------------------------------------------------

literalLoopBoundednessIsNotIndependent :
  S2Q.separateLiteralLoopBoundednessLeafRequired ≡ false
literalLoopBoundednessIsNotIndependent =
  S2Q.separateLiteralLoopBoundednessLeafRequiredIsFalse

multiplicationClosureIsNotIndependent :
  S2Q.separateBoundedMultiplicationClosureLeafRequired ≡ false
multiplicationClosureIsNotIndependent =
  S2Q.separateBoundedMultiplicationClosureLeafRequiredIsFalse

identityBoundednessIsNotIndependent :
  S2Q.separateIdentityBoundednessLeafRequired ≡ false
identityBoundednessIsNotIndependent =
  S2Q.separateIdentityBoundednessLeafRequiredIsFalse

quantitativeAttachmentRemainsPhysical :
  S2Q.singleQuantitativeBoundPredicateAttachmentStillPhysical ≡ true
quantitativeAttachmentRemainsPhysical =
  S2Q.singleQuantitativeBoundPredicateAttachmentStillPhysicalIsTrue

sameAlgebraAttachmentRemainsPhysical :
  S2Q.pointwiseMultiplyToT5MultiplySameObjectStillPhysical ≡ true
sameAlgebraAttachmentRemainsPhysical =
  S2Q.pointwiseMultiplyToT5MultiplySameObjectStillPhysicalIsTrue

supportTimeAttachmentRemainsPhysical :
  S2Q.supportDistanceTimeStillPhysical ≡ true
supportTimeAttachmentRemainsPhysical =
  S2Q.supportDistanceTimeStillPhysicalIsTrue

clayPromotionRemainsFalse :
  S2Q.clayPromotion ≡ false
clayPromotionRemainsFalse =
  S2Q.clayPromotionIsFalse
