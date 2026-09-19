module DASHI.Moonshine.JInvariantAnalyticStructuredPantsHyperformObserverExact where

------------------------------------------------------------------------
-- ANALYTIC j OBSERVER -> LOCAL 27 -> PANTS / HYPERFABRIC
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The analytic structured observer supplies a full finite jCoarse/jFine state.
-- Its existing downstream observer supplies one local 27 state.  This module
-- composes that local 27 with two already-owned finite geometries:
--
--   local 27 <-> Ternary27Point <-> PantsPath 3
--
-- and
--
--   local 27 as interaction voxel
--     + explicit appraisal-A / appraisal-B context
--     -> TernaryHyperformalPoint.
--
-- The first composition is a lossless finite change of coordinates.  The
-- second deliberately requires extra contextual fibre data: hyperfabric is not
-- inferred from the local 27 merely because both use ternary coordinates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact as Observer
import DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact as Residual
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as PantsBridge
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Topology.TernaryPantsFrontierExact as Pants

local27ToTernary27Point :
  Residual.LocalJ27 ->
  Fabric.Ternary27Point
local27ToTernary27Point ((first , second) , fine) =
  Fabric.ternary27Point
    (PantsBridge.kernelToSSP (PantsBridge.triTruthToKernel first))
    (PantsBridge.kernelToSSP (PantsBridge.triTruthToKernel second))
    (PantsBridge.kernelToSSP (PantsBridge.triTruthToKernel fine))

observeAnalyticInteractionVoxel :
  ∀ {system : Modular.ModularJFrickeSystem} ->
  Observer.AnalyticJStructuredObserver system ->
  Modular.FinePoint system ->
  Fabric.Ternary27Point
observeAnalyticInteractionVoxel observer point =
  local27ToTernary27Point (Observer.observeLocal27 observer point)

observeAnalyticPants3 :
  ∀ {system : Modular.ModularJFrickeSystem} ->
  Observer.AnalyticJStructuredObserver system ->
  Modular.FinePoint system ->
  Pants.PantsPath 3
observeAnalyticPants3 observer point =
  PantsBridge.voxel27ToPants3
    (observeAnalyticInteractionVoxel observer point)

record AnalyticHyperformContext : Set where
  constructor analytic-hyperform-context
  field
    appraisalA : Fabric.Ternary27Point
    appraisalB : Fabric.Ternary27Point

open AnalyticHyperformContext public

observeAnalyticHyperform :
  ∀ {system : Modular.ModularJFrickeSystem} ->
  Observer.AnalyticJStructuredObserver system ->
  Modular.FinePoint system ->
  AnalyticHyperformContext ->
  Fabric.TernaryHyperformalPoint
observeAnalyticHyperform observer point context =
  Fabric.ternaryHyperformalPoint
    (observeAnalyticInteractionVoxel observer point)
    (appraisalA context)
    (appraisalB context)

analyticHyperformProjectsToObservedInteraction :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : Observer.AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system)
    (context : AnalyticHyperformContext) ->
  Fabric.projectInteractionVoxel
    (observeAnalyticHyperform observer point context)
  ≡ observeAnalyticInteractionVoxel observer point
analyticHyperformProjectsToObservedInteraction observer point context = refl

analyticHyperformProjectsToExplicitContext :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observer : Observer.AnalyticJStructuredObserver system)
    (point : Modular.FinePoint system)
    (context : AnalyticHyperformContext) ->
  Fabric.projectAppraisalFibre
    (observeAnalyticHyperform observer point context)
  ≡ Fabric.appraisalFibrePoint
      (appraisalA context)
      (appraisalB context)
analyticHyperformProjectsToExplicitContext observer point context = refl

record AnalyticPantsHyperformBoundary : Set where
  constructor analytic-pants-hyperform-boundary
  field
    analyticToStructuredObserverRequired : Bool
    localTwentySevenToPantsThreeExact : Bool
    pantsThreeAddsNoExtraAnalyticInformation : Bool
    hyperfabricContextRequiredExplicitly : Bool
    localTwentySevenDeterminesAppraisalFibre : Bool
    finitePantsPathIsSmoothAnalyticPants : Bool

open AnalyticPantsHyperformBoundary public

canonicalAnalyticPantsHyperformBoundary :
  AnalyticPantsHyperformBoundary
canonicalAnalyticPantsHyperformBoundary =
  analytic-pants-hyperform-boundary
    true true true true false false
