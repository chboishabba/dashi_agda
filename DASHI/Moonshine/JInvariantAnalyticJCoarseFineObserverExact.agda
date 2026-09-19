module DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact where

------------------------------------------------------------------------
-- ANALYTIC MODULAR POINT -> FINITE jCOARSE/jFINE OBSERVER
--
-- DASHI CONTRIBUTION / REPAIR
--
-- The older AnalyticJCoarseFineFrickeEquivalence interface asks for a literal
-- two-sided equivalence between the analytic FinePoint carrier and the finite
-- 3^11 JTwoPlusNine chart.  That is appropriate only for a concrete finite
-- analytic model, not for an intended literal modular-curve carrier.
--
-- This owner keeps the exact finite Fricke machinery and weakens only the
-- analytic boundary to the mathematically appropriate observer shape:
--
--   analytic point
--       -> finite structured jCoarse/jFine observation
--
-- together with a Fricke intertwining law.  Information loss is represented
-- explicitly by the observer fibre.  No global inverse is required or inferred.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact as Chart
import DASHI.Moonshine.JInvariantJCoarseFineFrickeBoundaryTransportBidiExact as Finite

record AnalyticJStructuredObserver
    (system : Modular.ModularJFrickeSystem) : Set₁ where
  field
    observe :
      Modular.FinePoint system ->
      Chart.JTwoPlusNine

    frickeIntertwines :
      (point : Modular.FinePoint system) ->
      observe (Modular.fricke system point)
      ≡
      Finite.transportedFiniteFricke (observe point)

open AnalyticJStructuredObserver public

ObserverFibre :
  ∀ {system : Modular.ModularJFrickeSystem} ->
  AnalyticJStructuredObserver system ->
  Chart.JTwoPlusNine ->
  Modular.FinePoint system ->
  Set
ObserverFibre observer state point =
  observe observer point ≡ state

pointLiesInObservedFibre :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system) ->
  ObserverFibre observer (observe observer point) point
pointLiesInObservedFibre observer point = refl

frickeCarriesObserverFibre :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : AnalyticJStructuredObserver system)
    {state : Chart.JTwoPlusNine}
    {point : Modular.FinePoint system} ->
  ObserverFibre observer state point ->
  ObserverFibre
    observer
    (Finite.transportedFiniteFricke state)
    (Modular.fricke system point)
frickeCarriesObserverFibre observer {state} {point} inFibre =
  trans
    (frickeIntertwines observer point)
    (cong Finite.transportedFiniteFricke inFibre)

observedBoundaryExchange :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system) ->
  Finite.BoundaryExchangeReceipt (observe observer point)
observedBoundaryExchange observer point =
  Finite.canonicalBoundaryExchange (observe observer point)

record AnalyticObservedFrickeReceipt
    {system : Modular.ModularJFrickeSystem}
    (observer : AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system) : Set where
  constructor analytic-observed-fricke-receipt
  field
    sourceObservation : Chart.JTwoPlusNine
    sourceObservationIsPoint :
      sourceObservation ≡ observe observer point

    targetObservation : Chart.JTwoPlusNine
    targetObservationIsFiniteFricke :
      targetObservation
      ≡ Finite.transportedFiniteFricke sourceObservation

    targetObservationIsAnalyticFricke :
      targetObservation
      ≡ observe observer (Modular.fricke system point)

    boundaryExchange :
      Finite.BoundaryExchangeReceipt sourceObservation

open AnalyticObservedFrickeReceipt public

compileObservedFrickeReceipt :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system) ->
  AnalyticObservedFrickeReceipt observer point
compileObservedFrickeReceipt observer point =
  analytic-observed-fricke-receipt
    source
    refl
    (Finite.transportedFiniteFricke source)
    refl
    (sym (frickeIntertwines observer point))
    (Finite.canonicalBoundaryExchange source)
  where
    source = observe observer point

------------------------------------------------------------------------
-- Explicit authority boundary.
------------------------------------------------------------------------

record AnalyticJStructuredObserverBoundary : Set where
  constructor analytic-j-structured-observer-boundary
  field
    analyticToFiniteObservationRequired : Bool
    globalFiniteToAnalyticInverseRequired : Bool
    observerFibreRetained : Bool
    finiteFrickeBoundaryExchangeReused : Bool
    analyticFrickeIntertwiningRequired : Bool
    finiteObservationIsLiteralAnalyticPoint : Bool

open AnalyticJStructuredObserverBoundary public

canonicalAnalyticJStructuredObserverBoundary :
  AnalyticJStructuredObserverBoundary
canonicalAnalyticJStructuredObserverBoundary =
  analytic-j-structured-observer-boundary
    true false true true true false
