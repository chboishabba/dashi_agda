{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SingleSectorSharedSourceStressWeldValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119SingleSectorSharedSourceStressWeldExact as M

metricVariationNotMinimal :
  M.commonEinsteinMetricVariationRequiredOnMinimalSharedSourceRoute ≡ false
metricVariationNotMinimal = refl

commonMetricLanguageNotMinimal :
  M.commonMetricProducerLanguageRequiredOnMinimalSharedSourceRoute ≡ false
commonMetricLanguageNotMinimal = refl

directGRFactorisationRemains :
  M.directGRSourceFactorisationStillRequired ≡ true
directGRFactorisationRemains = refl
