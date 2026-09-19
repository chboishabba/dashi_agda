module DASHI.Moonshine.JInvariantAnalyticHyperformChartGluingExact where

------------------------------------------------------------------------
-- ANALYTIC EISENSTEIN CHART GLUING -> jCOARSE/jFINE -> PANTS/HYPERFABRIC
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- This module makes the architectural relation explicit without strengthening
-- any mathematical theorem.
--
-- Upstream:
--
--   q-series E4/E6 presentation
--          <same-object witness>
--   lattice E4/E6 presentation
--
-- Downstream:
--
--   analytic/modular fine point
--      -> structured jCoarse/jFine observation
--      -> local 27
--      -> PantsPath 3
--      -> contextual ternary hyperfabric.
--
-- The bridge between those layers is not inferred from shared notation.  A
-- caller must supply both the existing q-series/lattice same-object theorem and
-- an explicit map from the common analytic parameter into the modular FinePoint
-- carrier consumed by the structured observer.
--
-- In particular:
--
--   * analytic j is not identified with 369;
--   * a local-27 observer is not the whole fine modular point;
--   * PantsPath 3 is a finite coordinate change, not a smooth pair of pants;
--   * hyperfabric appraisal coordinates remain independent context.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Foundations.HyperformChartGluingExact as Glue
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Topology.TernaryPantsFrontierExact as Pants

import DASHI.Moonshine.JInvariantBishopLatticeEisensteinSameObjectCompilerExact as Lattice
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact as Chart
import DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact as Observer
import DASHI.Moonshine.JInvariantAnalyticStructuredPantsHyperformObserverExact as PantsObserver

record JInvariantAnalyticHyperformAtlas
    (M : Lattice.BishopLatticeEisensteinModel)
    (qE4 qE6 : Lattice.Parameter M → Complex.BishopComplex)
    (system : Modular.ModularJFrickeSystem) : Set₁ where
  field
    qSeriesLatticeSameObject :
      Lattice.BishopQSeriesLatticeSameObject M qE4 qE6

    parameterToFinePoint :
      Lattice.Parameter M →
      Modular.FinePoint system

    structuredObserver :
      Observer.AnalyticJStructuredObserver system

open JInvariantAnalyticHyperformAtlas public

------------------------------------------------------------------------
-- 1. q-series and lattice are explicit same-object charts.
------------------------------------------------------------------------

e4PresentationGluing :
  ∀ {M qE4 qE6 system} →
  JInvariantAnalyticHyperformAtlas M qE4 qE6 system →
  Glue.SameObjectChartGluing
    (Lattice.Parameter M)
    Complex.BishopComplex
    Complex._≈C_
e4PresentationGluing {M} {qE4} {qE6} atlas = record
  { Glue.chartA = qE4
  ; Glue.chartB = Lattice.BishopLatticeEisensteinSeries M 4
  ; Glue.glueOnOverlap =
      Lattice.e4SameObject (qSeriesLatticeSameObject atlas)
  }

e6PresentationGluing :
  ∀ {M qE4 qE6 system} →
  JInvariantAnalyticHyperformAtlas M qE4 qE6 system →
  Glue.SameObjectChartGluing
    (Lattice.Parameter M)
    Complex.BishopComplex
    Complex._≈C_
e6PresentationGluing {M} {qE4} {qE6} atlas = record
  { Glue.chartA = qE6
  ; Glue.chartB = Lattice.BishopLatticeEisensteinSeries M 6
  ; Glue.glueOnOverlap =
      Lattice.e6SameObject (qSeriesLatticeSameObject atlas)
  }

------------------------------------------------------------------------
-- 2. The modular/analytic point is observed coarsely with its fibre retained.
------------------------------------------------------------------------

parameterStructuredObserver :
  ∀ {M qE4 qE6 system} →
  JInvariantAnalyticHyperformAtlas M qE4 qE6 system →
  Glue.ObserverWithFibre
    (Lattice.Parameter M)
    Chart.JTwoPlusNine
parameterStructuredObserver atlas = record
  { Glue.observe = λ tau →
      Observer.observe
        (structuredObserver atlas)
        (parameterToFinePoint atlas tau)
  }

parameterLiesInObservedFibre :
  ∀ {M qE4 qE6 system}
    (atlas : JInvariantAnalyticHyperformAtlas M qE4 qE6 system)
    (tau : Lattice.Parameter M) →
  Glue.ObserverFibre
    (parameterStructuredObserver atlas)
    (Glue.observe (parameterStructuredObserver atlas) tau)
    tau
parameterLiesInObservedFibre atlas tau =
  Glue.pointLiesInOwnObserverFibre
    (parameterStructuredObserver atlas)
    tau

------------------------------------------------------------------------
-- 3. Local finite observer, pants coordinate, and contextual hyperfabric.
------------------------------------------------------------------------

observeInteractionAtParameter :
  ∀ {M qE4 qE6 system} →
  JInvariantAnalyticHyperformAtlas M qE4 qE6 system →
  Lattice.Parameter M →
  Fabric.Ternary27Point
observeInteractionAtParameter atlas tau =
  PantsObserver.observeAnalyticInteractionVoxel
    (structuredObserver atlas)
    (parameterToFinePoint atlas tau)

observePantsAtParameter :
  ∀ {M qE4 qE6 system} →
  JInvariantAnalyticHyperformAtlas M qE4 qE6 system →
  Lattice.Parameter M →
  Pants.PantsPath 3
observePantsAtParameter atlas tau =
  PantsObserver.observeAnalyticPants3
    (structuredObserver atlas)
    (parameterToFinePoint atlas tau)

analyticContextualFabricLift :
  ∀ {M qE4 qE6 system} →
  JInvariantAnalyticHyperformAtlas M qE4 qE6 system →
  Glue.ContextualFabricLift
    (Lattice.Parameter M)
    Fabric.Ternary27Point
    PantsObserver.AnalyticHyperformContext
    Fabric.TernaryHyperformalPoint
analyticContextualFabricLift atlas = record
  { Glue.observeLocal = observeInteractionAtParameter atlas
  ; Glue.assembleFabric = λ tau context →
      PantsObserver.observeAnalyticHyperform
        (structuredObserver atlas)
        (parameterToFinePoint atlas tau)
        context
  ; Glue.projectLocal = Fabric.projectInteractionVoxel
  ; Glue.projectLocalLaw = λ tau context →
      PantsObserver.analyticHyperformProjectsToObservedInteraction
        (structuredObserver atlas)
        (parameterToFinePoint atlas tau)
        context
  }

------------------------------------------------------------------------
-- 4. Authority / roadmap boundary.
------------------------------------------------------------------------

record JInvariantAnalyticHyperformAtlasBoundary : Set₁ where
  constructor j-invariant-analytic-hyperform-atlas-boundary
  field
    qSeriesLatticeSameObjectWitnessRequired : Bool
    analyticParameterToFinePointMapRequired : Bool
    structuredObserverRequired : Bool
    observerFibreRetained : Bool
    localTwentySevenIsDownstreamOnly : Bool
    pantsPathIsSmoothAnalyticPairOfPants : Bool
    hyperfabricContextInferredFromLocalTwentySeven : Bool
    shared369NumeralsIdentifyAnalyticJ : Bool
    bundleConstructsMissingFourierTheorem : Bool
    bundleConstructsMissingAnalyticJModuliIdentification : Bool

open JInvariantAnalyticHyperformAtlasBoundary public

canonicalJInvariantAnalyticHyperformAtlasBoundary :
  JInvariantAnalyticHyperformAtlasBoundary
canonicalJInvariantAnalyticHyperformAtlasBoundary =
  j-invariant-analytic-hyperform-atlas-boundary
    true true true true true false false false false false
