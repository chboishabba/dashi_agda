{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R274ToR387DirectUpperRound388Validation where

import DASHI.Physics.YangMills.BalabanCMP116R274ToR387DirectUpperRound388Exact as R388

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

_r274R284CompilesToR387 :
  R388.r274R284DirectProducerCompilesToR387 ≡ true
_r274R284CompilesToR387 = refl

_r274NotMandatory : R388.r274MandatoryForR387 ≡ false
_r274NotMandatory = refl

_noFreshEstimate : R388.r388IntroducesFreshYMEstimate ≡ false
_noFreshEstimate = refl
