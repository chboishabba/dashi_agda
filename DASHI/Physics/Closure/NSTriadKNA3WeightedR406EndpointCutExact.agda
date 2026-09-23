{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3WeightedR406EndpointCutExact where

------------------------------------------------------------------------
-- A3 / WEIGHTED R406 ENDPOINT CUT
--
-- Source archaeology after the endpoint-aware recut.
--
-- The live literal R406 carrier is resolvent-weighted.  The repository already
-- owns the exact weighted diagonal/temporal chain:
--
--   R557:
--     2 * integral R406
--       = integral factoredFull
--         - integral selfGram
--         - integral selfFluxTangent
--
--   R565/R570:
--     selfFluxTangent is the SAME global self-flux derivative and therefore
--     becomes an endpoint under ordinary scalar FTC.
--
--   R558/R568:
--     the initial self-flux is the SAME endpoint observable and has the
--     cardinality-free energy-square bound.
--
-- Consequently the endpoint/diagonal side is not a new NS estimate.
--
-- What is NOT presently proved is that A3's division-free signed pair-
-- difference scalar is definitionally or algebraically the R557/R567
-- resolvent-weighted factoredFull scalar.  The existing normalized quadratic
-- kernel collapse does not establish that equality.
--
-- This owner keeps that distinction explicit and prevents d1b0's unweighted
-- coherent-covariance identity from being silently substituted for the weighted
-- literal R406 normal form.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact as A3
import DASHI.Physics.Closure.NSTriadKNA3D1bDivisionFreeTransportExact as A3D1b
import DASHI.Physics.Closure.NSTriadKNR406ExactEndpointNormalFormExact as EndpointNF
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNGlobalSelfFluxEndpointRound558Exact as R558
import DASHI.Physics.Closure.NSTriadKNSelfFluxTemporalReconciliationRound565Exact as R565
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxEndpointWeldRound568Exact as R568Endpoint
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxTangentWeldRound570Exact as R570Tangent

------------------------------------------------------------------------
-- Already-closed endpoint/diagonal machinery.
------------------------------------------------------------------------

weightedIntegratedR406NormalFormClosed : Bool
weightedIntegratedR406NormalFormClosed =
  R557.round557LiveIntegratedNormalFormClosed


exactWeightedR406EndpointNormalFormClosedGivenFTC : Bool
exactWeightedR406EndpointNormalFormClosedGivenFTC =
  EndpointNF.r406ExactEndpointNormalFormClosedGivenScalarFTC

divisionFreeD1bA3NormalizationClosed : Bool
divisionFreeD1bA3NormalizationClosed =
  A3D1b.divisionFreeD1bA3NormalizationClosed

divisionFreeD1bA3MeanRateSelfWorkTermPresent : Bool
divisionFreeD1bA3MeanRateSelfWorkTermPresent =
  A3D1b.meanRateSelfWorkTermPresent

weightedSelfFluxNSDerivativeClosed : Bool
weightedSelfFluxNSDerivativeClosed =
  R565.round565NSDerivativeConstructionClosed

weightedSelfFluxTemporalOwnersReconciled : Bool
weightedSelfFluxTemporalOwnersReconciled =
  R565.round565ConcurrentTemporalOwnersReconciled

weightedSelfFluxTangentSameObjectWeldClosed : Bool
weightedSelfFluxTangentSameObjectWeldClosed =
  R570Tangent.round570GlobalSelfFluxTangentSameObjectWeldClosed

weightedInitialSelfFluxEndpointSameObjectWeldClosed : Bool
weightedInitialSelfFluxEndpointSameObjectWeldClosed =
  R568Endpoint.round568GlobalInitialSelfFluxSameObjectWeldClosed

weightedInitialSelfFluxEndpointBoundClosed : Bool
weightedInitialSelfFluxEndpointBoundClosed =
  R558.round558GlobalSelfFluxEndpointClosed

weightedEndpointIntroducesOutputCardinalityTax : Bool
weightedEndpointIntroducesOutputCardinalityTax =
  R558.round558OutputCardinalityTaxIntroduced

------------------------------------------------------------------------
-- A3 comparison boundary.
------------------------------------------------------------------------

a3NormalizedQuadraticKernelAggregateBridgeClosed : Bool
a3NormalizedQuadraticKernelAggregateBridgeClosed =
  A3.a3NormalizedQuadraticKernelAggregateBridgeClosed

-- The aggregate kernel collapse is useful structure, but it does not identify
-- A3's division-free pair-difference work with the literal R567 factored-full
-- Cauchy-resolvent scalar.
a3PairDifferenceIsLiteralFactoredFullSameObjectClosed : Bool
a3PairDifferenceIsLiteralFactoredFullSameObjectClosed = false

unweightedD1b0DirectlyPaysWeightedR406Pointwise : Bool
unweightedD1b0DirectlyPaysWeightedR406Pointwise = false

weightedR406EndpointSideRequiresNewNonlinearEstimate : Bool
weightedR406EndpointSideRequiresNewNonlinearEstimate = false

weightedR406EndpointSideStillRequiresScalarFTC : Bool
weightedR406EndpointSideStillRequiresScalarFTC =
  not R565.round565ConcreteScalarFTCInhabitantInstalled
  where
  not : Bool → Bool
  not true = false
  not false = true

------------------------------------------------------------------------
-- Exact proof flags.
------------------------------------------------------------------------

weightedIntegratedR406NormalFormClosedIsTrue :
  weightedIntegratedR406NormalFormClosed ≡ true
weightedIntegratedR406NormalFormClosedIsTrue =
  R557.round557LiveIntegratedNormalFormClosedIsTrue


exactWeightedR406EndpointNormalFormClosedGivenFTCIsTrue :
  exactWeightedR406EndpointNormalFormClosedGivenFTC ≡ true
exactWeightedR406EndpointNormalFormClosedGivenFTCIsTrue =
  EndpointNF.r406ExactEndpointNormalFormClosedGivenScalarFTCIsTrue

divisionFreeD1bA3NormalizationClosedIsTrue :
  divisionFreeD1bA3NormalizationClosed ≡ true
divisionFreeD1bA3NormalizationClosedIsTrue =
  A3D1b.divisionFreeD1bA3NormalizationClosedIsTrue

divisionFreeD1bA3MeanRateSelfWorkTermPresentIsTrue :
  divisionFreeD1bA3MeanRateSelfWorkTermPresent ≡ true
divisionFreeD1bA3MeanRateSelfWorkTermPresentIsTrue =
  A3D1b.meanRateSelfWorkTermPresentIsTrue

weightedSelfFluxNSDerivativeClosedIsTrue :
  weightedSelfFluxNSDerivativeClosed ≡ true
weightedSelfFluxNSDerivativeClosedIsTrue =
  R565.round565NSDerivativeConstructionClosedIsTrue

weightedSelfFluxTemporalOwnersReconciledIsTrue :
  weightedSelfFluxTemporalOwnersReconciled ≡ true
weightedSelfFluxTemporalOwnersReconciledIsTrue =
  R565.round565ConcurrentTemporalOwnersReconciledIsTrue

weightedSelfFluxTangentSameObjectWeldClosedIsTrue :
  weightedSelfFluxTangentSameObjectWeldClosed ≡ true
weightedSelfFluxTangentSameObjectWeldClosedIsTrue =
  R570Tangent.round570GlobalSelfFluxTangentSameObjectWeldClosedIsTrue

weightedInitialSelfFluxEndpointSameObjectWeldClosedIsTrue :
  weightedInitialSelfFluxEndpointSameObjectWeldClosed ≡ true
weightedInitialSelfFluxEndpointSameObjectWeldClosedIsTrue =
  R568Endpoint.round568GlobalInitialSelfFluxSameObjectWeldClosedIsTrue

weightedInitialSelfFluxEndpointBoundClosedIsTrue :
  weightedInitialSelfFluxEndpointBoundClosed ≡ true
weightedInitialSelfFluxEndpointBoundClosedIsTrue =
  R558.round558GlobalSelfFluxEndpointClosedIsTrue

weightedEndpointIntroducesOutputCardinalityTaxIsFalse :
  weightedEndpointIntroducesOutputCardinalityTax ≡ false
weightedEndpointIntroducesOutputCardinalityTaxIsFalse =
  R558.round558OutputCardinalityTaxIntroducedIsFalse

a3NormalizedQuadraticKernelAggregateBridgeClosedIsTrue :
  a3NormalizedQuadraticKernelAggregateBridgeClosed ≡ true
a3NormalizedQuadraticKernelAggregateBridgeClosedIsTrue =
  A3.a3NormalizedQuadraticKernelAggregateBridgeClosedIsTrue

a3PairDifferenceIsLiteralFactoredFullSameObjectClosedIsFalse :
  a3PairDifferenceIsLiteralFactoredFullSameObjectClosed ≡ false
a3PairDifferenceIsLiteralFactoredFullSameObjectClosedIsFalse = refl

unweightedD1b0DirectlyPaysWeightedR406PointwiseIsFalse :
  unweightedD1b0DirectlyPaysWeightedR406Pointwise ≡ false
unweightedD1b0DirectlyPaysWeightedR406PointwiseIsFalse = refl

weightedR406EndpointSideRequiresNewNonlinearEstimateIsFalse :
  weightedR406EndpointSideRequiresNewNonlinearEstimate ≡ false
weightedR406EndpointSideRequiresNewNonlinearEstimateIsFalse = refl
