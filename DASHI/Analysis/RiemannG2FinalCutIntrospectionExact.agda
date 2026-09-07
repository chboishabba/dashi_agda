module DASHI.Analysis.RiemannG2FinalCutIntrospectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannG2FinalPoleQuotientMinimalAnalyticCutExact as Cut
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as NearObserver

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
-- SECOND-LEVEL INTROSPECTION: OBSERVER INSIDE THE LIVE SCALAR LEAF
--
-- The terminal leaf mentions D_near(J), but the current final transport exposes
-- that object only through the scalar `nearResponseAt J`.  Existing count and
-- absolute-envelope observations identify states whose signed contributions
-- differ.  Therefore before a phase-sensitive proof route can be reused, the
-- observer must expose the literal target-relative phase on the exact final
-- near carrier.
------------------------------------------------------------------------

data RHInnerCoordinate : Set where
  abstractFinalNearScalar : RHInnerCoordinate
  countAndAbsoluteEnvelope : RHInnerCoordinate
  finalNearLiteralPhaseRealisation : RHInnerCoordinate
  fullWeilTargetWindowRealisation : RHInnerCoordinate
  independentJointComplementPayment : RHInnerCoordinate


data RHInnerState : Set where
  inadequateObservation : RHInnerState
  firstMissingCoordinate : RHInnerState
  optionalStrongerRefinement : RHInnerState
  theoremPayment : RHInnerState

innerState : RHInnerCoordinate -> RHInnerState
innerState abstractFinalNearScalar = inadequateObservation
innerState countAndAbsoluteEnvelope = inadequateObservation
innerState finalNearLiteralPhaseRealisation = firstMissingCoordinate
innerState fullWeilTargetWindowRealisation = optionalStrongerRefinement
innerState independentJointComplementPayment = theoremPayment

currentInnerMissingCoordinate : RHInnerCoordinate
currentInnerMissingCoordinate = finalNearLiteralPhaseRealisation

currentInnerMissingCoordinateIsFirst :
  innerState currentInnerMissingCoordinate ≡ firstMissingCoordinate
currentInnerMissingCoordinateIsFirst = refl

nearObserverAgreesPhaseIsFirstMissingCoordinate :
  NearObserver.FinalPoleNearObserverRefinementBoundary.targetRelativePhaseIsFirstMissingCoordinate
    NearObserver.canonicalFinalPoleNearObserverRefinementBoundary ≡ true
nearObserverAgreesPhaseIsFirstMissingCoordinate = refl

nearObserverAgreesFullWeilWindowIsStrongerThanPrimitiveNeed :
  NearObserver.FinalPoleNearObserverRefinementBoundary.fullWeilTargetWindowIsPrimitiveRequirementOfOneLeafConsumer
    NearObserver.canonicalFinalPoleNearObserverRefinementBoundary ≡ false
nearObserverAgreesFullWeilWindowIsStrongerThanPrimitiveNeed = refl

nearObserverAgreesLiteralModelIsNotPayment :
  NearObserver.FinalPoleNearObserverRefinementBoundary.literalModelAutomaticallyPaysJointMargin
    NearObserver.canonicalFinalPoleNearObserverRefinementBoundary ≡ false
nearObserverAgreesLiteralModelIsNotPayment = refl

record BoundRHInnerRefinement : Set where
  constructor bound-rh-inner-refinement
  field
    parentDemand : BoundRHFinalDemand
    parentIsCurrentDemand : parentDemand ≡ currentBoundRHFinalDemand
    missingCoordinate : RHInnerCoordinate
    missingCoordinateIsCurrent : missingCoordinate ≡ currentInnerMissingCoordinate
    refinementRequired : Bool
    refinementRequiredIsTrue : refinementRequired ≡ true
    refinementPaysAnalyticMargin : Bool
    refinementPaysAnalyticMarginIsFalse : refinementPaysAnalyticMargin ≡ false

currentBoundRHInnerRefinement : BoundRHInnerRefinement
currentBoundRHInnerRefinement =
  bound-rh-inner-refinement
    currentBoundRHFinalDemand
    refl
    finalNearLiteralPhaseRealisation
    refl
    true refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RepresentationTransportPaysAnalyticMargin : Set where
data FinalBalancePaysAnalyticMargin : Set where
data VisualizationPaysAnalyticMargin : Set where
data BoundProducerPaysAnalyticMargin : Set where
data LiteralNearRefinementPaysAnalyticMargin : Set where

representationTransportDoesNotPayAnalyticMargin :
  RepresentationTransportPaysAnalyticMargin → ⊥
representationTransportDoesNotPayAnalyticMargin ()

finalBalanceDoesNotPayAnalyticMargin : FinalBalancePaysAnalyticMargin → ⊥
finalBalanceDoesNotPayAnalyticMargin ()

visualizationDoesNotPayAnalyticMargin : VisualizationPaysAnalyticMargin → ⊥
visualizationDoesNotPayAnalyticMargin ()

boundProducerDoesNotPayAnalyticMargin : BoundProducerPaysAnalyticMargin → ⊥
boundProducerDoesNotPayAnalyticMargin ()

literalNearRefinementDoesNotPayAnalyticMargin :
  LiteralNearRefinementPaysAnalyticMargin → ⊥
literalNearRefinementDoesNotPayAnalyticMargin ()
