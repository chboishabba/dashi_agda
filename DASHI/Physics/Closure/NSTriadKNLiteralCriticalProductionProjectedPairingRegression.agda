module DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionProjectedPairingRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionProjectedPairingExact as Subject

literalProductionPairingSameObjectIsClosed :
  Subject.literalCriticalProductionProjectedPairingSameObjectClosed ≡ true
literalProductionPairingSameObjectIsClosed =
  Subject.literalCriticalProductionProjectedPairingSameObjectClosedIsTrue

r98ProjectedPairingCarrierIsReused :
  Subject.r98LiteralProjectedPairingCarrierReused ≡ true
r98ProjectedPairingCarrierIsReused =
  Subject.r98LiteralProjectedPairingCarrierReusedIsTrue

s2EstimateStillOpen :
  Subject.s2LiteralSignedProductionEstimateClosed ≡ false
s2EstimateStillOpen =
  Subject.s2LiteralSignedProductionEstimateClosedIsFalse
