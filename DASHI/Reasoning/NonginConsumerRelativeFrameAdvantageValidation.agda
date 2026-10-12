module DASHI.Reasoning.NonginConsumerRelativeFrameAdvantageValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.NonginConsumerRelativeFrameAdvantageExact as Nongin

boundary : Nongin.NonginConsumerRelativeFrameAdvantageBoundary
boundary = Nongin.canonicalNonginConsumerRelativeFrameAdvantageBoundary

consumerRelativeNonfactorabilityPaid :
  Nongin.consumerRelativeNonfactorabilityPaid boundary ≡ true
consumerRelativeNonfactorabilityPaid = refl

nondistinguishingCollisionDoesNotPayAdvantage :
  Nongin.nondistinguishingCollisionPaysAdvantage boundary ≡ false
nondistinguishingCollisionDoesNotPayAdvantage = refl

exactConsumerRepairPaid :
  Nongin.exactConsumerRecoveryPaid boundary ≡ true
exactConsumerRepairPaid = refl

literalTenPercentLawNotPromoted :
  Nongin.literalTenPercentLawPromoted boundary ≡ false
literalTenPercentLawNotPromoted = refl
