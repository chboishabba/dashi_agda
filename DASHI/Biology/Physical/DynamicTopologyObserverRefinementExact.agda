module DASHI.Biology.Physical.DynamicTopologyObserverRefinementExact where

------------------------------------------------------------------------
-- DYNAMIC TOPOLOGY AS AN OBSERVER-REFINEMENT WITNESS
--
-- The existing biological theorem exhibits two states with equal present
-- morphology but different hidden junctions, for which the same future signal
-- yields different morphology.  Here the junction is treated as the next
-- observer coordinate.  It strictly refines morphology and the resulting pair
-- observer separates the concrete graph state, hence is future-language safe.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.DynamicTopologyFutureDefectExact as Topology
import DASHI.Core.ObserverRefinementFutureSafetyExact as FutureBridge
import DASHI.Core.ObserverRefinementLatticeExact as Observer

junctionObserver : Observer.Observer Topology.GraphDevelopmentalState Bool
junctionObserver = Topology.junction

morphologyJunctionObserver :
  Observer.Observer Topology.GraphDevelopmentalState (Bool × Bool)
morphologyJunctionObserver =
  Observer.pairObserver Topology.morphologyProjection junctionObserver

morphologyPlusJunctionStrictlyRefinesMorphology :
  Observer.StrictRefinement
    Topology.morphologyProjection
    morphologyJunctionObserver
morphologyPlusJunctionStrictlyRefinesMorphology =
  Observer.strictPairRefinement
    Topology.morphologyProjection
    junctionObserver
    Topology.withoutJunction
    Topology.withJunction
    Topology.sameVisibleMorphology
    Topology.hiddenTopologyDiffers

morphologyProjectionCannotSeparateGraphState :
  Observer.Separating Topology.morphologyProjection → ⊥
morphologyProjectionCannotSeparateGraphState =
  Observer.strictFamilyRefinementBlocksCoarseSeparation
    (Observer.strictFamilyRefinement
      (λ x y pairSame → cong proj₁ pairSame)
      Topology.withoutJunction
      Topology.withJunction
      Topology.sameVisibleMorphology
      (λ pairSame → Topology.hiddenTopologyDiffers (cong proj₂ pairSame)))
