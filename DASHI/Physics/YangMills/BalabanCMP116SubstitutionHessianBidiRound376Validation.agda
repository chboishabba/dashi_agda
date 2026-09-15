module DASHI.Physics.YangMills.BalabanCMP116SubstitutionHessianBidiRound376Validation where

------------------------------------------------------------------------
-- ROUND376 RED / H_sub -> R375 BIDI REGRESSION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.YangMills.BalabanCMP116SubstitutionHessianBidiRound376Exact as R376

round376HSubFeedsR375 :
  R376.hSubAttachmentFeedsHessianBidi ≡ true
round376HSubFeedsR375 = R376.hSubAttachmentFeedsHessianBidiIsTrue

round376DistanceUpperNotPrimitive :
  R376.separateDistanceToMarkedInputPrimitiveAfterRound376 ≡ false
round376DistanceUpperNotPrimitive =
  R376.separateDistanceToMarkedInputPrimitiveAfterRound376IsFalse

round376CoordinateWeldStillRequired :
  R376.boundaryDistanceCoordinateWeldStillRequired ≡ true
round376CoordinateWeldStillRequired =
  R376.boundaryDistanceCoordinateWeldStillRequiredIsTrue
