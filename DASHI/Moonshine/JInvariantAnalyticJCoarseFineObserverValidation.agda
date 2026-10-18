module DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverValidation where

import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact as Chart
import DASHI.Moonshine.JInvariantJCoarseFineFrickeBoundaryTransportBidiExact as Finite
import DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact as Residual
import DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact as P

observeFrickeRegression :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : P.AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system) →
  P.observe observer (Modular.fricke system point)
  ≡ Finite.transportedFiniteFricke (P.observe observer point)
observeFrickeRegression = P.frickeIntertwines

observedPointInOwnFibre :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : P.AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system) →
  P.ObserverFibre observer (P.observe observer point) point
observedPointInOwnFibre = P.pointLiesInObservedFibre

observerCompilesBoundaryReceipt :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : P.AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system) →
  Finite.BoundaryExchangeReceipt (P.observe observer point)
observerCompilesBoundaryReceipt =
  P.observedBoundaryExchange

local27IsDownstreamRegression :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : P.AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system) →
  P.observeLocal27 observer point
  ≡ Residual.localJObserver (P.observeStructuredField observer point)
local27IsDownstreamRegression =
  P.local27IsDownstreamObserver
