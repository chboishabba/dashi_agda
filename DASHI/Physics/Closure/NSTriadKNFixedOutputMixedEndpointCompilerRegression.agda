module DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as S

regressionLiteralRHSWeld :
  S.literalRHSFixedOutputDampedTangentWeldClosed ≡ true
regressionLiteralRHSWeld =
  S.literalRHSFixedOutputDampedTangentWeldClosedIsTrue

regressionFiniteEndpointDerivative :
  S.fixedOutputMixedEndpointDerivativeCompilerClosed ≡ true
regressionFiniteEndpointDerivative =
  S.fixedOutputMixedEndpointDerivativeCompilerClosedIsTrue

regressionEndpointGivenFTC :
  S.fixedOutputEndpointIdentityClosedGivenCalculus ≡ true
regressionEndpointGivenFTC =
  S.fixedOutputEndpointIdentityClosedGivenCalculusIsTrue

regressionConcreteFTCStillOpen :
  S.concreteEndpointFTCInstalled ≡ false
regressionConcreteFTCStillOpen =
  S.concreteEndpointFTCInstalledIsFalse

regressionCovarianceStillOpen :
  S.quantitativeCoherentCovariancePaymentClosed ≡ false
regressionCovarianceStillOpen =
  S.quantitativeCoherentCovariancePaymentClosedIsFalse
