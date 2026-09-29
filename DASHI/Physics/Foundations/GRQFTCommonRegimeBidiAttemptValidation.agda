{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCommonRegimeBidiAttemptValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.GRQFTCommonRegimeBidiAttemptExact as A

promotionDoesNotBlockExecution :
  A.missingCommonRegimePromotionTokenBlocksAttemptExecution ≡ false
promotionDoesNotBlockExecution = refl

fourFailureCoordinatesRetained :
  A.commonRegimeAttemptRetainsFourSeparateFailureCoordinates ≡ true
fourFailureCoordinatesRetained = refl
