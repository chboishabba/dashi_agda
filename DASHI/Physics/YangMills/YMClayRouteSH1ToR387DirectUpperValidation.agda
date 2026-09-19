{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSH1ToR387DirectUpperValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayRouteSH1ToR387DirectUpperExact as Route

noSourceEnvelope :
  Route.sourceEnvelopeRequiredBetweenH1AndR387 ≡ false
noSourceEnvelope = refl

noSourceRootDistanceCarrier :
  Route.sourceRootOrDistanceCarrierRequiredBetweenH1AndR387 ≡ false
noSourceRootDistanceCarrier = refl

timeMeaningStaysSeparate :
  Route.selectedTimeMeaningRemainsOutsideH1 ≡ true
timeMeaningStaysSeparate = refl

fastEnvelopeMeaningStaysSeparate :
  Route.selectedFastEnvelopeMeaningRemainsOutsideH1 ≡ true
fastEnvelopeMeaningStaysSeparate = refl

promotionFailClosed :
  Route.clayPromotion ≡ false
promotionFailClosed = refl
