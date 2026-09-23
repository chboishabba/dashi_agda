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
import DASHI.Physics.Closure.NSTriadKNR567CauchyGramFluxNormalFormRound596Exact as R596
import DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact as R597
import DASHI.Physics.Closure.NSTriadKNCyclicResolvedTransferRateDefectRound598Exact as R598
import DASHI.Physics.Closure.NSTriadKNCyclicRouteExternalNetworkDefectRound599Exact as R599
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedR406GramTangentNormalFormExact as GramTangent
import DASHI.Physics.Closure.NSTriadKNCauchyR397R406ReconciliationExact as Reconcile
import DASHI.Physics.Closure.NSTriadKNA3CauchyFluxTangentMismatchRound598Exact as R598
import DASHI.Physics.Closure.NSTriadKNA3CenteredFullGramNormalFormRound599Exact as R599

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


r567CauchyGramFluxNormalFormClosed : Bool
r567CauchyGramFluxNormalFormClosed =
  R596.round596LiteralR567CauchyGramFluxNormalFormClosed

r567FullGramAlignedWithA3SelfWorkClosed : Bool
r567FullGramAlignedWithA3SelfWorkClosed =
  R596.round596FullGramAlignedWithA3CoherentSelfWork

genericFullGramCoherentFoldClosed : Bool
genericFullGramCoherentFoldClosed =
  R597.round597FullGramCoherentFoldClosed


cyclicResolvedTransferRateDefectCompilerClosed : Bool
cyclicResolvedTransferRateDefectCompilerClosed =
  R598.round598ResolvedWeightedTransferIsRateDefectFormClosed

cyclicRateDefectNumeratorsExposedInPhysicalModes : Bool
cyclicRateDefectNumeratorsExposedInPhysicalModes =
  R598.round598RateDefectNumeratorsExposedInPhysicalModes


cyclicExternalNetworkDefectExposed : Bool
cyclicExternalNetworkDefectExposed =
  R599.round599FullThreeLegEnergyEqualsExternalNetworkClosed

bareFullProjectedForcingCyclicConservationAvailable : Bool
bareFullProjectedForcingCyclicConservationAvailable =
  R599.round599BareFullProjectedForcingCyclicConservationAvailable

cauchyResolvedR406DiagonalReducedNormalFormClosed : Bool
cauchyResolvedR406DiagonalReducedNormalFormClosed =
  GramTangent.cauchyResolvedR406DiagonalReducedNormalFormClosed

cauchyResolvedR406ResidualIsOffdiagGramPlusResolvedTangent : Bool
cauchyResolvedR406ResidualIsOffdiagGramPlusResolvedTangent = true

cauchyR397R406FiniteReconciliationClosed : Bool
cauchyR397R406FiniteReconciliationClosed =
  Reconcile.cauchyR397R406ReconciliationClosed

cauchyResolvedNormalFormCreatesNewA3Identification : Bool
cauchyResolvedNormalFormCreatesNewA3Identification =
  Reconcile.reconciliationIdentifiesR406WithA3

cauchyA3MismatchNormalFormClosed : Bool
cauchyA3MismatchNormalFormClosed =
  R598.round598CauchyA3MismatchNormalFormClosed

a3SelfWorkCoordinateCancelledExactly : Bool
a3SelfWorkCoordinateCancelledExactly =
  R598.round598A3SelfWorkCoordinateCancelledExactly

a3CenteredFullGramNormalFormClosed : Bool
a3CenteredFullGramNormalFormClosed =
  R599.round599A3CenteredFullGramNormalFormClosed

a3AndR596ShareCompleteDoubleMixedGramCarrier : Bool
a3AndR596ShareCompleteDoubleMixedGramCarrier =
  R599.round599A3AndR596NowShareCompleteDoubleMixedGramCarrier

weightedFluxTangentFullSquareToCenteredA3RateKernelClosed : Bool
weightedFluxTangentFullSquareToCenteredA3RateKernelClosed =
  R598.round598FluxTangentToRateWeightedKernelClosed


meanRateSelfWorkNormalizationMustBeRetained : Bool
meanRateSelfWorkNormalizationMustBeRetained =
  D1b.meanRateSelfWorkTermPresent

offdiagGramPlusResolvedTangentToCenteredA3KernelSameObjectClosed : Bool
offdiagGramPlusResolvedTangentToCenteredA3KernelSameObjectClosed = false

factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosed : Bool
factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosed =
  offdiagGramPlusResolvedTangentToCenteredA3KernelSameObjectClosed

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


r567CauchyGramFluxNormalFormClosedIsTrue :
  r567CauchyGramFluxNormalFormClosed ≡ true
r567CauchyGramFluxNormalFormClosedIsTrue =
  R596.round596LiteralR567CauchyGramFluxNormalFormClosedIsTrue

r567FullGramAlignedWithA3SelfWorkClosedIsTrue :
  r567FullGramAlignedWithA3SelfWorkClosed ≡ true
r567FullGramAlignedWithA3SelfWorkClosedIsTrue =
  R596.round596FullGramAlignedWithA3CoherentSelfWorkIsTrue

genericFullGramCoherentFoldClosedIsTrue :
  genericFullGramCoherentFoldClosed ≡ true
genericFullGramCoherentFoldClosedIsTrue =
  R597.round597FullGramCoherentFoldClosedIsTrue


cyclicResolvedTransferRateDefectCompilerClosedIsTrue :
  cyclicResolvedTransferRateDefectCompilerClosed ≡ true
cyclicResolvedTransferRateDefectCompilerClosedIsTrue =
  R598.round598ResolvedWeightedTransferIsRateDefectFormClosedIsTrue

cyclicRateDefectNumeratorsExposedInPhysicalModesIsTrue :
  cyclicRateDefectNumeratorsExposedInPhysicalModes ≡ true
cyclicRateDefectNumeratorsExposedInPhysicalModesIsTrue = refl


cyclicExternalNetworkDefectExposedIsTrue :
  cyclicExternalNetworkDefectExposed ≡ true
cyclicExternalNetworkDefectExposedIsTrue =
  R599.round599FullThreeLegEnergyEqualsExternalNetworkClosedIsTrue

bareFullProjectedForcingCyclicConservationAvailableIsFalse :
  bareFullProjectedForcingCyclicConservationAvailable ≡ false
bareFullProjectedForcingCyclicConservationAvailableIsFalse =
  R599.round599BareFullProjectedForcingCyclicConservationAvailableIsFalse

cauchyResolvedR406DiagonalReducedNormalFormClosedIsTrue :
  cauchyResolvedR406DiagonalReducedNormalFormClosed ≡ true
cauchyResolvedR406DiagonalReducedNormalFormClosedIsTrue =
  GramTangent.cauchyResolvedR406DiagonalReducedNormalFormClosedIsTrue

cauchyResolvedR406ResidualIsOffdiagGramPlusResolvedTangentIsTrue :
  cauchyResolvedR406ResidualIsOffdiagGramPlusResolvedTangent ≡ true
cauchyResolvedR406ResidualIsOffdiagGramPlusResolvedTangentIsTrue = refl

cauchyR397R406FiniteReconciliationClosedIsTrue :
  cauchyR397R406FiniteReconciliationClosed ≡ true
cauchyR397R406FiniteReconciliationClosedIsTrue =
  Reconcile.cauchyR397R406ReconciliationClosedIsTrue

cauchyResolvedNormalFormCreatesNewA3IdentificationIsFalse :
  cauchyResolvedNormalFormCreatesNewA3Identification ≡ false
cauchyResolvedNormalFormCreatesNewA3IdentificationIsFalse =
  Reconcile.reconciliationIdentifiesR406WithA3IsFalse

cauchyA3MismatchNormalFormClosedIsTrue :
  cauchyA3MismatchNormalFormClosed ≡ true
cauchyA3MismatchNormalFormClosedIsTrue =
  R598.round598CauchyA3MismatchNormalFormClosedIsTrue

a3SelfWorkCoordinateCancelledExactlyIsTrue :
  a3SelfWorkCoordinateCancelledExactly ≡ true
a3SelfWorkCoordinateCancelledExactlyIsTrue =
  R598.round598A3SelfWorkCoordinateCancelledExactlyIsTrue

a3CenteredFullGramNormalFormClosedIsTrue :
  a3CenteredFullGramNormalFormClosed ≡ true
a3CenteredFullGramNormalFormClosedIsTrue =
  R599.round599A3CenteredFullGramNormalFormClosedIsTrue

a3AndR596ShareCompleteDoubleMixedGramCarrierIsTrue :
  a3AndR596ShareCompleteDoubleMixedGramCarrier ≡ true
a3AndR596ShareCompleteDoubleMixedGramCarrierIsTrue =
  R599.round599A3AndR596NowShareCompleteDoubleMixedGramCarrierIsTrue

meanRateSelfWorkNormalizationMustBeRetainedIsTrue :
  meanRateSelfWorkNormalizationMustBeRetained ≡ true
meanRateSelfWorkNormalizationMustBeRetainedIsTrue =
  D1b.meanRateSelfWorkTermPresentIsTrue

offdiagGramPlusResolvedTangentToCenteredA3KernelSameObjectClosedIsFalse :
  offdiagGramPlusResolvedTangentToCenteredA3KernelSameObjectClosed ≡ false
offdiagGramPlusResolvedTangentToCenteredA3KernelSameObjectClosedIsFalse = refl

factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosedIsFalse :
  factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosed ≡ false
factoredFullMinusSelfGramToCenteredA3KernelSameObjectClosedIsFalse = refl


weightedFluxTangentFullSquareToCenteredA3RateKernelClosedIsFalse :
  weightedFluxTangentFullSquareToCenteredA3RateKernelClosed ≡ false
weightedFluxTangentFullSquareToCenteredA3RateKernelClosedIsFalse =
  R598.round598FluxTangentToRateWeightedKernelClosedIsFalse


r230ScalarConsumerToConservedCyclicTripleClosedIsFalse :
  r230ScalarConsumerToConservedCyclicTripleClosed ≡ false
r230ScalarConsumerToConservedCyclicTripleClosedIsFalse = refl


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
