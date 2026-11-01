{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF1TranslatedPairL2CalibrationValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayF1TranslatedPairL2CalibrationExact as F1C

envelopeEqualityIsNotPrimitive :
  F1C.independentEnvelopeEqualityRequired ≡ false
envelopeEqualityIsNotPrimitive =
  F1C.independentEnvelopeEqualityRequiredIsFalse

diagonalPairIsNotTheTransferPair :
  F1C.diagonalSameObservablePairSuffices ≡ false
diagonalPairIsNotTheTransferPair =
  F1C.diagonalSameObservablePairSufficesIsFalse

translatedOneStepPairIsCanonical :
  F1C.translatedOneStepPairIsCanonical ≡ true
translatedOneStepPairIsCanonical =
  F1C.translatedOneStepPairIsCanonicalIsTrue

f1CIsOneSidedContraction :
  F1C.remainingF1CIsOneSidedPhysicalContraction ≡ true
f1CIsOneSidedContraction =
  F1C.remainingF1CIsOneSidedPhysicalContractionIsTrue

noClayPromotion :
  F1C.clayPromotion ≡ false
noClayPromotion = F1C.clayPromotionIsFalse
