{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySelectedR109FiniteExpectationFromSelectedPresentationTest where

import DASHI.Physics.Foundations.CMP119CosmologySelectedR109FiniteExpectationFromSelectedPresentationExact as Subject

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

noFunctionalPairEvaluator :
  Subject.finiteExpectationConsumerNeedsFunctionalPairEvaluator ≡ false
noFunctionalPairEvaluator = refl

samePinnedFamily :
  Subject.finiteExpectationStillUsesPinnedOSFamily ≡ true
samePinnedFamily = refl
