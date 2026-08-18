module DASHI.Biology.Physical.DynamicTopologyObserverRefinementExact where

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.DynamicTopologyFutureDefectExact as Topology
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ObserverRefinementFutureSafetyExact as FutureBridge
import DASHI.Core.ObserverRefinementLatticeExact as Observer

junctionObserver : Observer.Observer Topology.GraphDevelopmentalState Bool
junctionObserver = Topology.junction

morphologyJunctionObserver :
  Observer.Observer Topology.GraphDevelopmentalState (Bool × Bool)
morphologyJunctionObserver =
  Observer.pairObserver Topology.morphologyProjection junctionObserver

morphologyPlusJunctionStrictlyRefinesMorphology :
  Observer.StrictRefinement Topology.morphologyProjection morphologyJunctionObserver
morphologyPlusJunctionStrictlyRefinesMorphology =
  Observer.strictPairRefinement
    Topology.morphologyProjection junctionObserver
    Topology.withoutJunction Topology.withJunction
    Topology.sameVisibleMorphology Topology.hiddenTopologyDiffers

morphologyJunctionSeparatesGraphState :
  Observer.Separating morphologyJunctionObserver
morphologyJunctionSeparatesGraphState
  (Topology.graphDevelopmentalState lm lj)
  (Topology.graphDevelopmentalState rm rj)
  same
  with cong proj₁ same | cong proj₂ same
... | refl | refl = refl

morphologyJunctionIsFutureLanguageSafe :
  Future.FutureLanguageSafeProjection
    Topology.system Topology.morphologyProjection morphologyJunctionObserver
morphologyJunctionIsFutureLanguageSafe =
  FutureBridge.separatingObserverIsFutureLanguageSafe
    morphologyJunctionSeparatesGraphState

-- This is the positive repair companion to the existing exact theorem
-- `morphologyWithoutTopologyIsNotFutureSafe`.
