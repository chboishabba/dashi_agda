{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB4PhysicalR440UniformTargetTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSCanonicalB4PhysicalR440UniformTargetExact as T

fixedRationalArithmetic : T.b4UniformTargetUsesLiteralRationals ≡ true
fixedRationalArithmetic = T.b4UniformTargetUsesLiteralRationalsIsTrue

uniformConstants : T.b4UniformThetaAndCoefficientAreStateCutoffOutputIndependent ≡ true
uniformConstants = T.b4UniformThetaAndCoefficientAreStateCutoffOutputIndependentIsTrue

thetaBounded : T.b4UniformTargetRequiresThetaInHalfOpenInterval ≡ true
thetaBounded = T.b4UniformTargetRequiresThetaInHalfOpenIntervalIsTrue

coefficientBounded : T.b4UniformTargetRequiresNonnegativeEDCoefficient ≡ true
coefficientBounded = T.b4UniformTargetRequiresNonnegativeEDCoefficientIsTrue

physicalMassBounded : T.b4UniformTargetRequiresCoreMassNonnegative ≡ true
physicalMassBounded = T.b4UniformTargetRequiresCoreMassNonnegativeIsTrue

localEDBounded : T.b4UniformTargetRequiresLocalEDNonnegative ≡ true
localEDBounded = T.b4UniformTargetRequiresLocalEDNonnegativeIsTrue

admissibleCutoffRequired : T.b4UniformTargetRequiresAdmissibleCutoff ≡ true
admissibleCutoffRequired = T.b4UniformTargetRequiresAdmissibleCutoffIsTrue

sourceAttachmentRequired : T.b4UniformTargetRequiresSameSourceAttachments ≡ true
sourceAttachmentRequired = T.b4UniformTargetRequiresSameSourceAttachmentsIsTrue

keyLemmaStillOpen : T.b4UniformPhysicalR440PaymentClosed ≡ false
keyLemmaStillOpen = T.b4UniformPhysicalR440PaymentClosedIsFalse
