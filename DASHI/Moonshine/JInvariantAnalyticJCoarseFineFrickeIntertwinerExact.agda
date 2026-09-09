module DASHI.Moonshine.JInvariantAnalyticJCoarseFineFrickeIntertwinerExact where

------------------------------------------------------------------------
-- ANALYTIC MODULAR POINT <-> STRUCTURED jCOARSE/jFINE FRICKE COMPILER
--
-- The repository already owns:
--   * an abstract analytic ModularJFrickeSystem with an involutive Fricke map;
--   * the exact finite 2+9 jCoarse/jFine carrier;
--   * the exact transported finite Fricke boundary exchange.
--
-- This owner closes the theorem layer between them.  A concrete analytic
-- realization must provide one SAME-OBJECT equivalence and one intertwining
-- receipt.  Once supplied, structured acquisition and analytic<->finite
-- Fricke transport are compiler-owned; no second theorem socket remains.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact as Chart
import DASHI.Moonshine.JInvariantJCoarseFineFrickeBoundaryTransportBidiExact as Finite

record AnalyticJCoarseFineFrickeEquivalence
  (system : Modular.ModularJFrickeSystem) : Set₁ where
  field
    toStructured : Modular.FinePoint system → Chart.JTwoPlusNine
    fromStructured : Chart.JTwoPlusNine → Modular.FinePoint system
    fromAfterTo :
      (point : Modular.FinePoint system) →
      fromStructured (toStructured point) ≡ point
    toAfterFrom :
      (state : Chart.JTwoPlusNine) →
      toStructured (fromStructured state) ≡ state
    frickeIntertwines :
      (point : Modular.FinePoint system) →
      toStructured (Modular.fricke system point)
      ≡ Finite.transportedFiniteFricke (toStructured point)

open AnalyticJCoarseFineFrickeEquivalence public

analyticCoordinateToStructuredJField :
  {system : Modular.ModularJFrickeSystem} →
  AnalyticJCoarseFineFrickeEquivalence system →
  Modular.FinePoint system →
  Chart.JTwoPlusNine
analyticCoordinateToStructuredJField = toStructured

structuredJFieldToAnalyticCoordinate :
  {system : Modular.ModularJFrickeSystem} →
  AnalyticJCoarseFineFrickeEquivalence system →
  Chart.JTwoPlusNine →
  Modular.FinePoint system
structuredJFieldToAnalyticCoordinate = fromStructured

analyticFrickeToFiniteBoundaryExchange :
  {system : Modular.ModularJFrickeSystem} →
  (bridge : AnalyticJCoarseFineFrickeEquivalence system) →
  (point : Modular.FinePoint system) →
  toStructured bridge (Modular.fricke system point)
  ≡ Finite.transportedFiniteFricke (toStructured bridge point)
analyticFrickeToFiniteBoundaryExchange = frickeIntertwines

finiteBoundaryExchangeToAnalyticFricke :
  {system : Modular.ModularJFrickeSystem} →
  (bridge : AnalyticJCoarseFineFrickeEquivalence system) →
  (state : Chart.JTwoPlusNine) →
  fromStructured bridge (Finite.transportedFiniteFricke state)
  ≡ Modular.fricke system (fromStructured bridge state)
finiteBoundaryExchangeToAnalyticFricke {system} bridge state =
  let point = fromStructured bridge state
      chartRoundTrip = toAfterFrom bridge state
  in
  trans
    (cong (fromStructured bridge)
      (cong Finite.transportedFiniteFricke (sym chartRoundTrip)))
    (trans
      (cong (fromStructured bridge)
        (sym (frickeIntertwines bridge point)))
      (fromAfterTo bridge (Modular.fricke system point)))

record AnalyticFrickeBoundaryExchangeReceipt
  {system : Modular.ModularJFrickeSystem}
  (bridge : AnalyticJCoarseFineFrickeEquivalence system)
  (point : Modular.FinePoint system) : Set where
  constructor analytic-fricke-boundary-exchange-receipt
  field
    structuredState : Chart.JTwoPlusNine
    structuredStateIsPoint : structuredState ≡ toStructured bridge point
    transportedState : Chart.JTwoPlusNine
    transportedStateIsFiniteFricke :
      transportedState ≡ Finite.transportedFiniteFricke structuredState
    transportedStateIsAnalyticFricke :
      transportedState ≡ toStructured bridge (Modular.fricke system point)
    boundaryExchange : Finite.BoundaryExchangeReceipt structuredState

open AnalyticFrickeBoundaryExchangeReceipt public

compileAnalyticFrickeBoundaryExchange :
  {system : Modular.ModularJFrickeSystem} →
  (bridge : AnalyticJCoarseFineFrickeEquivalence system) →
  (point : Modular.FinePoint system) →
  AnalyticFrickeBoundaryExchangeReceipt bridge point
compileAnalyticFrickeBoundaryExchange bridge point =
  let state = toStructured bridge point
  in
  analytic-fricke-boundary-exchange-receipt
    state
    refl
    (Finite.transportedFiniteFricke state)
    refl
    (sym (frickeIntertwines bridge point))
    (Finite.canonicalBoundaryExchange state)

record AnalyticJCoarseFineFrickeClosure : Set where
  constructor analytic-jcoarse-jfine-fricke-closure
  field
    analyticToStructuredCompilerExact : Bool
    structuredToAnalyticCompilerExact : Bool
    twoSidedSameObjectLawsRequired : Bool
    analyticFrickeFiniteTransportCompilerExact : Bool
    finiteBoundaryExchangeReceiptReused : Bool
    concreteAnalyticEquivalenceInventedHere : Bool

canonicalAnalyticJCoarseFineFrickeClosure : AnalyticJCoarseFineFrickeClosure
canonicalAnalyticJCoarseFineFrickeClosure =
  analytic-jcoarse-jfine-fricke-closure
    true true true true true false
