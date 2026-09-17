module DASHI.Physics.Closure.NSTriadKNS2b2d1b2QuantitativePaymentRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true)

import DASHI.Physics.Closure.NSTriadKNS2b2d1b2QuantitativePaymentExact as Payment

-- RED-first contract: production must provide a same-object quantitative
-- S2b2d1b2 owner before this regression can typecheck.
quantitativePaymentClosed : Payment.s2b2d1b2QuantitativePaymentClosed ≡ true
quantitativePaymentClosed = Payment.s2b2d1b2QuantitativePaymentClosedIsTrue

fourSignResidualConsumed : Payment.s2b2d1b2ConsumesLiteralFourSignGramResidual ≡ true
fourSignResidualConsumed = Payment.s2b2d1b2ConsumesLiteralFourSignGramResidualIsTrue

r571EnvelopeConsumed : Payment.s2b2d1b2ConsumesR571Envelope ≡ true
r571EnvelopeConsumed = Payment.s2b2d1b2ConsumesR571EnvelopeIsTrue

r568AdapterConstructed : Payment.s2b2d1b2R568AdapterConstructed ≡ true
r568AdapterConstructed = Payment.s2b2d1b2R568AdapterConstructedIsTrue

cutoffIndependentConstants : Payment.s2b2d1b2ConstantsCutoffIndependent ≡ true
cutoffIndependentConstants = Payment.s2b2d1b2ConstantsCutoffIndependentIsTrue
