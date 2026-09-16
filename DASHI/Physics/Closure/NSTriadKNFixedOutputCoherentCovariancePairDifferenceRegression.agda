module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as S

regressionFiniteCenteringIdentity :
  S.divisionFreePairDifferenceCenteringClosed ≡ true
regressionFiniteCenteringIdentity =
  S.divisionFreePairDifferenceCenteringClosedIsTrue

regressionPhysicalFixedOutputAttachment :
  S.fixedOutputCovariancePairDifferenceAttachmentClosed ≡ true
regressionPhysicalFixedOutputAttachment =
  S.fixedOutputWorkDifferenceVectorBridgeClosed ≡ true

regressionWorkDifferenceVectorBridge :
  S.fixedOutputWorkDifferenceVectorBridgeClosed ≡ true
regressionWorkDifferenceVectorBridge =
  S.fixedOutputWorkDifferenceVectorBridgeClosedIsTrue

regressionQuantitativePairDifferencePaymentStillOpen :
  S.quantitativePairDifferencePaymentClosed ≡ false
regressionQuantitativePairDifferencePaymentStillOpen =
  S.quantitativePairDifferencePaymentClosedIsFalse
