{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3AsymptoticFiniteF2CommonLimitValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP3AsymptoticFiniteF2CommonLimitExact as P3

termwiseFiniteF2EqualityNotRequiredRegression :
  P3.termwiseFiniteF2EqualityRequired ≡ false
termwiseFiniteF2EqualityNotRequiredRegression = refl

vanishingFiniteF2BridgeSufficesRegression :
  P3.vanishingFiniteF2BridgeSufficesForCommonLimit ≡ true
vanishingFiniteF2BridgeSufficesRegression = refl

oldPointwiseQ3IsZeroErrorSpecialCaseRegression :
  P3.oldPointwiseQ3IsZeroErrorSpecialCase ≡ true
oldPointwiseQ3IsZeroErrorSpecialCaseRegression = refl

q3SourcePaymentReducedRegression :
  P3.q3ReducedToAsymptoticFiniteF2Bridge ≡ true
q3SourcePaymentReducedRegression = refl
