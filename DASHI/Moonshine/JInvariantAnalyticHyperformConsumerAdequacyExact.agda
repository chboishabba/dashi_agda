module DASHI.Moonshine.JInvariantAnalyticHyperformConsumerAdequacyExact where

------------------------------------------------------------------------
-- ANALYTIC jCOARSE/jFINE OBSERVER: CONSUMER ADEQUACY THROUGH PANTS
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The analytic hyperfabric atlas now exposes:
--
--   Parameter -> JTwoPlusNine -> local 27 -> PantsPath 3.
--
-- This module makes the information-flow consequence proof-relevant.  The
-- local-27 and pants surfaces are post-compositions of the structured finite
-- observation.  Therefore they can be excellent coordinates for consumers
-- that factor through them, but they cannot reconstruct a distinction already
-- erased by the upstream observer.
--
-- The theorem is consumer-indexed.  It does not say that JTwoPlusNine, local27,
-- or pants are globally lossy or globally sufficient.
------------------------------------------------------------------------

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Foundations.HyperformChartGluingExact as Glue
import DASHI.Foundations.HyperformObserverFactorisationExact as Factor
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Topology.TernaryPantsFrontierExact as Pants

import DASHI.Moonshine.JInvariantAnalyticHyperformChartGluingExact as Atlas
import DASHI.Moonshine.JInvariantAnalyticStructuredPantsHyperformObserverExact as PantsObserver
import DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact as Chart
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinSameObjectCompilerExact as Lattice

interactionRechart :
  Chart.JTwoPlusNine →
  Fabric.Ternary27Point
interactionRechart =
  PantsObserver.chartToInteractionVoxel

pantsRechart :
  Chart.JTwoPlusNine →
  Pants.PantsPath 3
pantsRechart =
  PantsObserver.chartToPants3

parameterInteractionObserver :
  ∀ {M qE4 qE6 system} →
  Atlas.JInvariantAnalyticHyperformAtlas M qE4 qE6 system →
  Glue.ObserverWithFibre
    (Lattice.Parameter M)
    Fabric.Ternary27Point
parameterInteractionObserver atlas =
  Factor.rechartObserver
    (Atlas.parameterStructuredObserver atlas)
    interactionRechart

parameterPantsObserver :
  ∀ {M qE4 qE6 system} →
  Atlas.JInvariantAnalyticHyperformAtlas M qE4 qE6 system →
  Glue.ObserverWithFibre
    (Lattice.Parameter M)
    (Pants.PantsPath 3)
parameterPantsObserver atlas =
  Factor.rechartObserver
    (Atlas.parameterStructuredObserver atlas)
    pantsRechart

interactionObserverAgreesWithAtlas :
  ∀ {M qE4 qE6 system}
    (atlas : Atlas.JInvariantAnalyticHyperformAtlas M qE4 qE6 system)
    (tau : Lattice.Parameter M) →
  Glue.observe (parameterInteractionObserver atlas) tau
  ≡ Atlas.observeInteractionAtParameter atlas tau
interactionObserverAgreesWithAtlas atlas tau = refl

pantsObserverAgreesWithAtlas :
  ∀ {M qE4 qE6 system}
    (atlas : Atlas.JInvariantAnalyticHyperformAtlas M qE4 qE6 system)
    (tau : Lattice.Parameter M) →
  Glue.observe (parameterPantsObserver atlas) tau
  ≡ Atlas.observePantsAtParameter atlas tau
pantsObserverAgreesWithAtlas atlas tau = refl

interactionCannotRecoverStructuredObserverDistinction :
  ∀ {M qE4 qE6 system Outcome}
    (atlas : Atlas.JInvariantAnalyticHyperformAtlas M qE4 qE6 system)
    {consumer : Lattice.Parameter M → Outcome} →
  INF.NonFactorabilityWitness
    (Glue.observe (Atlas.parameterStructuredObserver atlas))
    consumer →
  INF.FactorsThrough
    (Glue.observe (parameterInteractionObserver atlas))
    consumer →
  ⊥
interactionCannotRecoverStructuredObserverDistinction atlas =
  Factor.rechartCannotRecoverObserverFibreDistinction
    (Atlas.parameterStructuredObserver atlas)
    interactionRechart

pantsCannotRecoverStructuredObserverDistinction :
  ∀ {M qE4 qE6 system Outcome}
    (atlas : Atlas.JInvariantAnalyticHyperformAtlas M qE4 qE6 system)
    {consumer : Lattice.Parameter M → Outcome} →
  INF.NonFactorabilityWitness
    (Glue.observe (Atlas.parameterStructuredObserver atlas))
    consumer →
  INF.FactorsThrough
    (Glue.observe (parameterPantsObserver atlas))
    consumer →
  ⊥
pantsCannotRecoverStructuredObserverDistinction atlas =
  Factor.rechartCannotRecoverObserverFibreDistinction
    (Atlas.parameterStructuredObserver atlas)
    pantsRechart

record JInvariantAnalyticHyperformConsumerBoundary : Set where
  constructor j-invariant-analytic-hyperform-consumer-boundary
  field
    structuredObserverAdequateForEveryConsumer : Bool
    localInteractionIsPostcomposition : Bool
    pantsThreeIsPostcomposition : Bool
    pantsCanRecoverErasedStructuredDistinction : Bool
    consumerSpecificFactorisationCanStillEstablishAdequacy : Bool
    richerHyperformContextRequiresSeparateConsumerAnalysis : Bool

open JInvariantAnalyticHyperformConsumerBoundary public

canonicalJInvariantAnalyticHyperformConsumerBoundary :
  JInvariantAnalyticHyperformConsumerBoundary
canonicalJInvariantAnalyticHyperformConsumerBoundary =
  j-invariant-analytic-hyperform-consumer-boundary
    false true true false true true
