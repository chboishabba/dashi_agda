module DASHI.Physics.Closure.NSTriadKNS2b2d1b2QuantitativePaymentRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNS2b2d1b2QuantitativePaymentExact as Payment

------------------------------------------------------------------------
-- GREEN regression for the implemented SAME-OBJECT spine.
--
-- The previous RED contract incorrectly required the still-open quantitative
-- estimate itself to be true.  The repository contract is stronger and safer:
-- exact physical plumbing must be inhabited, while each analytic payment stays
-- fail-closed until a theorem inhabitant exists.
------------------------------------------------------------------------

sameObjectSpineClosed : Payment.s2b2d1b2SameObjectSpineClosed ≡ true
sameObjectSpineClosed = Payment.s2b2d1b2SameObjectSpineClosedIsTrue

coherentCovarianceAttached :
  Payment.s2b2d1b2CoherentCovarianceAttachmentClosed ≡ true
coherentCovarianceAttached =
  Payment.s2b2d1b2CoherentCovarianceAttachmentClosedIsTrue

r571FiniteCompilerAttached :
  Payment.s2b2d1b2R571FiniteSecondMomentCompilerClosed ≡ true
r571FiniteCompilerAttached =
  Payment.s2b2d1b2R571FiniteSecondMomentCompilerClosedIsTrue

literalFourSignCarrierAttached :
  Payment.s2b2d1b2LiteralFourSignGramCarrierAttached ≡ true
literalFourSignCarrierAttached =
  Payment.s2b2d1b2LiteralFourSignGramCarrierAttachedIsTrue

r568ConditionalCompilerAttached :
  Payment.s2b2d1b2R568ConditionalCompilerAttached ≡ true
r568ConditionalCompilerAttached =
  Payment.s2b2d1b2R568ConditionalCompilerAttachedIsTrue

quantitativePaymentStillOpen :
  Payment.s2b2d1b2QuantitativePaymentClosed ≡ false
quantitativePaymentStillOpen = Payment.s2b2d1b2QuantitativePaymentClosedIsFalse

fourSignResidualStillOpen :
  Payment.s2b2d1b2ConsumesLiteralFourSignGramResidual ≡ false
fourSignResidualStillOpen =
  Payment.s2b2d1b2ConsumesLiteralFourSignGramResidualIsFalse

r571StateEnvelopeStillOpen :
  Payment.s2b2d1b2ConsumesR571Envelope ≡ false
r571StateEnvelopeStillOpen = Payment.s2b2d1b2ConsumesR571EnvelopeIsFalse

r568SpecificAdapterStillOpen :
  Payment.s2b2d1b2R568AdapterConstructed ≡ false
r568SpecificAdapterStillOpen = Payment.s2b2d1b2R568AdapterConstructedIsFalse

cutoffIndependentConstantsStillOpen :
  Payment.s2b2d1b2ConstantsCutoffIndependent ≡ false
cutoffIndependentConstantsStillOpen =
  Payment.s2b2d1b2ConstantsCutoffIndependentIsFalse
