module DASHI.Moonshine.JInvariantAnalyticStructuredPantsHyperformObserverValidation where

import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact as Observer
import DASHI.Moonshine.JInvariantAnalyticStructuredPantsHyperformObserverExact as P
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Topology.TernaryPantsFrontierExact as Pants

analyticPantsRegression :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : Observer.AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system) →
  Pants.PantsPath 3
analyticPantsRegression = P.observeAnalyticPants3

interactionProjectionRegression :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : Observer.AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system)
    (context : P.AnalyticHyperformContext) →
  Fabric.projectInteractionVoxel
    (P.observeAnalyticHyperform observer point context)
  ≡ P.observeAnalyticInteractionVoxel observer point
interactionProjectionRegression = P.analyticHyperformProjectsToObservedInteraction
