{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTTheoryValidationSplitValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.RecoveryCommutationCoreExact as R
import DASHI.Physics.Foundations.CommonRegimeMathematicalCoreExact as C
import DASHI.Physics.Foundations.GRQFTTheoryValidationSplitExact as S

fullRecoveryReceiptNotSameObjectPremise :
  R.fullGRRecoveryReceiptRequiredForSameObjectEquality ≡ false
fullRecoveryReceiptNotSameObjectPremise = refl

regimeTokenNotOverlapMath :
  C.regimePromotionTokenIsMathematicalOverlapPremise ≡ false
regimeTokenNotOverlapMath = refl

w4NotTheoryPremise :
  S.w4DrellYanIsPremiseOfMathematicalGRQFTCore ≡ false
w4NotTheoryPremise = refl

commonRegimeIsTheoryCore :
  S.commonRegimeBackreactionIsPartOfTheoryCore ≡ true
commonRegimeIsTheoryCore = refl
