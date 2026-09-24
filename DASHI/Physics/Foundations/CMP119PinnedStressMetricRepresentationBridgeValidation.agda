{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119PinnedStressMetricRepresentationBridgeValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.CMP119PinnedStressMetricRepresentationBridgeExact as B

noSecondRepresentationStressTheorem :
  B.secondEndpointToMetricStressIdentificationRequired ≡ false
noSecondRepresentationStressTheorem = refl
