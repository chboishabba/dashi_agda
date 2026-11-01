module DASHI.Physics.Closure.NSTriadKNS2b2d1b2QuantitativePaymentStatusExact where

open import Agda.Builtin.Bool using (Bool)

import DASHI.Physics.Closure.NSTriadKNS2b2d1b2QuantitativePaymentExact as Payment

-- Separate status surface so downstream coordinators can depend on the
-- quantitative owner without duplicating its proof terms.
s2b2d1b2QuantitativePaymentStatus : Bool
s2b2d1b2QuantitativePaymentStatus = Payment.s2b2d1b2QuantitativePaymentClosed
