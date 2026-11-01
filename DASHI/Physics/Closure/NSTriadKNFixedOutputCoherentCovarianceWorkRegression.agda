module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as S

regressionFixedOutputWorkDecomposition :
  S.fixedOutputCommutatorWorkDecompositionClosed ≡ true
regressionFixedOutputWorkDecomposition =
  S.fixedOutputCommutatorWorkDecompositionClosedIsTrue

regressionCommonRateCovarianceIsolation :
  S.commonRateCoherentCovarianceIsolationClosed ≡ true
regressionCommonRateCovarianceIsolation =
  S.commonRateCoherentCovarianceIsolationClosedIsTrue

regressionQuantitativeCovarianceStillOpen :
  S.quantitativeCoherentCovariancePaymentClosed ≡ false
regressionQuantitativeCovarianceStillOpen =
  S.quantitativeCoherentCovariancePaymentClosedIsFalse
