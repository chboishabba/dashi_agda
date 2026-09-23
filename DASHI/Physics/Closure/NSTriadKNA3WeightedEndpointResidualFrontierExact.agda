{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3WeightedEndpointResidualFrontierExact where

------------------------------------------------------------------------
-- CANONICAL A3 / WEIGHTED-R406 ENDPOINT RESIDUAL FRONTIER
--
-- Closed side A:
--   exact live weighted R406 endpoint normal form
--
--     2 * integral R406
--       = (integral FactoredFull - integral SelfGram)
--         - (SelfFlux(T) - SelfFlux(0)).
--
-- Closed side B:
--   exact division-free A3 centered-kernel normal form
--
--     4 * A3Signed
--       = n * (-W(M,K_r)) + rateTotal * W(M,K).
--
-- Neither closed theorem identifies its centered weighted-kernel scalar with
-- the R547/R550 FactoredFull - SelfGram scalar. Repository search found no
-- exact same-object theorem paying that coordinate.
--
-- Therefore the honest representation residual is:
--
--   (FactoredFull - SelfGram)
--       <-> centered A3 kernel scalar
--
-- with all fibre-cardinality / mean-rate normalization retained explicitly.
-- This is a representation theorem, not a second nonlinear estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNA3D1bDivisionFreeTransportExact as D1b
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelPaymentCompilerExact as KernelPay
import DASHI.Physics.Closure.NSTriadKNR406ExactEndpointNormalFormExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNA3WeightedR406EndpointCutExact as WeightedCut
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact as Cauchy

weightedR406ExactEndpointNormalFormClosedGivenFTC : Bool
weightedR406ExactEndpointNormalFormClosedGivenFTC =
  Endpoint.r406ExactEndpointNormalFormClosedGivenScalarFTC

a3DivisionFreeNormalizationClosed : Bool
a3DivisionFreeNormalizationClosed =
  D1b.divisionFreeD1bA3NormalizationClosed

a3CenteredKernelNormalFormClosed : Bool
a3CenteredKernelNormalFormClosed =
  Kernel.a3KernelCenteredNormalFormClosed

a3CenteredKernelPaymentCompilerClosed : Bool
a3CenteredKernelPaymentCompilerClosed =
  KernelPay.kernelCenteredPaymentCompilerClosed


cauchyResolvedFullSquareRateCancellationClosed : Bool
cauchyResolvedFullSquareRateCancellationClosed =
  Cauchy.cauchyResolvedFullSquareRateCancellationClosed

literalNonzeroOutputPairResolventRateCancellationClosed : Bool
literalNonzeroOutputPairResolventRateCancellationClosed =
  Cauchy.literalNonzeroOutputPairResolventRateCancellationClosed

meanRateSelfWorkNormalizationMustBeRetained : Bool
meanRateSelfWorkNormalizationMustBeRetained =
  D1b.meanRateSelfWorkTermPresent

factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosed : Bool
factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosed = false

cauchyRateCancellationAloneClosesCenteredA3ToR568 : Bool
cauchyRateCancellationAloneClosesCenteredA3ToR568 = false

thisResidualIsAdditionalNonlinearEstimate : Bool
thisResidualIsAdditionalNonlinearEstimate = false

naiveUnitCoefficientEndpointPlusA3IdentityAdmissible : Bool
naiveUnitCoefficientEndpointPlusA3IdentityAdmissible = false

directUnweightedCovarianceEqualsWeightedR406Admissible : Bool
directUnweightedCovarianceEqualsWeightedR406Admissible =
  WeightedCut.unweightedD1b0DirectlyPaysWeightedR406Pointwise

weightedR406ExactEndpointNormalFormClosedGivenFTCIsTrue :
  weightedR406ExactEndpointNormalFormClosedGivenFTC ≡ true
weightedR406ExactEndpointNormalFormClosedGivenFTCIsTrue =
  Endpoint.r406ExactEndpointNormalFormClosedGivenScalarFTCIsTrue

a3DivisionFreeNormalizationClosedIsTrue :
  a3DivisionFreeNormalizationClosed ≡ true
a3DivisionFreeNormalizationClosedIsTrue =
  D1b.divisionFreeD1bA3NormalizationClosedIsTrue

a3CenteredKernelNormalFormClosedIsTrue :
  a3CenteredKernelNormalFormClosed ≡ true
a3CenteredKernelNormalFormClosedIsTrue =
  Kernel.a3KernelCenteredNormalFormClosedIsTrue

a3CenteredKernelPaymentCompilerClosedIsTrue :
  a3CenteredKernelPaymentCompilerClosed ≡ true
a3CenteredKernelPaymentCompilerClosedIsTrue =
  KernelPay.kernelCenteredPaymentCompilerClosedIsTrue


cauchyResolvedFullSquareRateCancellationClosedIsTrue :
  cauchyResolvedFullSquareRateCancellationClosed ≡ true
cauchyResolvedFullSquareRateCancellationClosedIsTrue =
  Cauchy.cauchyResolvedFullSquareRateCancellationClosedIsTrue

literalNonzeroOutputPairResolventRateCancellationClosedIsTrue :
  literalNonzeroOutputPairResolventRateCancellationClosed ≡ true
literalNonzeroOutputPairResolventRateCancellationClosedIsTrue =
  Cauchy.literalNonzeroOutputPairResolventRateCancellationClosedIsTrue

meanRateSelfWorkNormalizationMustBeRetainedIsTrue :
  meanRateSelfWorkNormalizationMustBeRetained ≡ true
meanRateSelfWorkNormalizationMustBeRetainedIsTrue =
  D1b.meanRateSelfWorkTermPresentIsTrue

factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosedIsFalse :
  factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosed ≡ false
factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosedIsFalse = refl


cauchyRateCancellationAloneClosesCenteredA3ToR568IsFalse :
  cauchyRateCancellationAloneClosesCenteredA3ToR568 ≡ false
cauchyRateCancellationAloneClosesCenteredA3ToR568IsFalse = refl

thisResidualIsAdditionalNonlinearEstimateIsFalse :
  thisResidualIsAdditionalNonlinearEstimate ≡ false
thisResidualIsAdditionalNonlinearEstimateIsFalse = refl

naiveUnitCoefficientEndpointPlusA3IdentityAdmissibleIsFalse :
  naiveUnitCoefficientEndpointPlusA3IdentityAdmissible ≡ false
naiveUnitCoefficientEndpointPlusA3IdentityAdmissibleIsFalse = refl

directUnweightedCovarianceEqualsWeightedR406AdmissibleIsFalse :
  directUnweightedCovarianceEqualsWeightedR406Admissible ≡ false
directUnweightedCovarianceEqualsWeightedR406AdmissibleIsFalse =
  WeightedCut.unweightedD1b0DirectlyPaysWeightedR406PointwiseIsFalse
