module DASHI.Analysis.RiemannG2FinalCutIntrospectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannG2FinalPoleQuotientMinimalAnalyticCutExact as Cut

------------------------------------------------------------------------
-- INTROSPECTIVE BINDING FOR THE CURRENT RH HIGH-ZERO SCALAR LEAF
--
-- The final cut has already pruned the separate near/Gamma allowance leaves.
-- The surviving analytic theorem is exactly the independent literal complement
-- margin.  This owner prevents adjacent representation/downstream coordinates
-- or a visually compelling decomposition from being counted as payment.
------------------------------------------------------------------------

data RHFinalProducer : Set where
  independentLiteralComplementMarginProducer : RHFinalProducer
  crossProverTransportProducer : RHFinalProducer
  downstreamBalanceProducer : RHFinalProducer

producerForCoordinate : Cut.FinalCutCoordinate → RHFinalProducer
producerForCoordinate Cut.proveIndependentLiteralComplementMargin =
  independentLiteralComplementMarginProducer
producerForCoordinate Cut.transportCheckedLeanSplitFarToAgda =
  crossProverTransportProducer
producerForCoordinate Cut.sourceOrderReflexivity =
  crossProverTransportProducer
producerForCoordinate Cut.transportFinalSourceOrders =
  downstreamBalanceProducer
producerForCoordinate Cut.attachFinalClusterSameObject =
  downstreamBalanceProducer
producerForCoordinate Cut.assignConsumerChannelAllowances =
  downstreamBalanceProducer
producerForCoordinate Cut.proveChosenFiniteNearUpper =
  downstreamBalanceProducer
producerForCoordinate Cut.proveFreshGammaEnvelope =
  downstreamBalanceProducer
producerForCoordinate Cut.proveChosenNearLeavesFarAllowance =
  downstreamBalanceProducer
producerForCoordinate Cut.proveGammaFitsAssignedAllowance =
  downstreamBalanceProducer
producerForCoordinate Cut.rebuildNearFarBudgetFamilyForEveryCutoff =
  downstreamBalanceProducer
producerForCoordinate Cut.recoverDeterminantDirectPayment =
  downstreamBalanceProducer
producerForCoordinate Cut.rebuildFinalContradiction =
  downstreamBalanceProducer

record BoundRHFinalDemand : Set where
  constructor bound-rh-final-demand
  field
    liveCoordinate : Cut.FinalCutCoordinate
    liveCoordinateIsTerminalAnalyticLeaf :
      liveCoordinate ≡ Cut.proveIndependentLiteralComplementMargin
    coordinateClassIsAnalytic : Cut.coordinateClass liveCoordinate ≡ Cut.analytic
    producer : RHFinalProducer
    producerMatchesCoordinate : producer ≡ producerForCoordinate liveCoordinate
    analyticPaymentEstablished : Bool
    analyticPaymentEstablishedIsFalse : analyticPaymentEstablished ≡ false

open BoundRHFinalDemand public

currentBoundRHFinalDemand : BoundRHFinalDemand
currentBoundRHFinalDemand =
  bound-rh-final-demand
    Cut.proveIndependentLiteralComplementMargin
    refl
    refl
    independentLiteralComplementMarginProducer
    refl
    false
    refl

currentRHProducerTargetsExactAnalyticLeaf :
  producer currentBoundRHFinalDemand ≡ independentLiteralComplementMarginProducer
currentRHProducerTargetsExactAnalyticLeaf = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RepresentationTransportPaysAnalyticMargin : Set where
data FinalBalancePaysAnalyticMargin : Set where
data VisualizationPaysAnalyticMargin : Set where
data BoundProducerPaysAnalyticMargin : Set where

representationTransportDoesNotPayAnalyticMargin :
  RepresentationTransportPaysAnalyticMargin → ⊥
representationTransportDoesNotPayAnalyticMargin ()

finalBalanceDoesNotPayAnalyticMargin : FinalBalancePaysAnalyticMargin → ⊥
finalBalanceDoesNotPayAnalyticMargin ()

visualizationDoesNotPayAnalyticMargin : VisualizationPaysAnalyticMargin → ⊥
visualizationDoesNotPayAnalyticMargin ()

boundProducerDoesNotPayAnalyticMargin : BoundProducerPaysAnalyticMargin → ⊥
boundProducerDoesNotPayAnalyticMargin ()
