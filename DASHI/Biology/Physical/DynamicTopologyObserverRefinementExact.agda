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

withoutWithJunctionDistinct :
  Topology.withoutJunction ≡ Topology.withJunction → ⊥
withoutWithJunctionDistinct same =
  Topology.hiddenTopologyDiffers (cong Topology.junction same)

morphologyCollision :
  Observer.ObserverCollision Topology.morphologyProjection
morphologyCollision =
  Observer.observerCollision
    Topology.withoutJunction
    Topology.withJunction
    Topology.sameVisibleMorphology
    withoutWithJunctionDistinct

morphologyProjectionCannotSeparateGraphState :
  Observer.Separating Topology.morphologyProjection → ⊥
morphologyProjectionCannotSeparateGraphState =
  Observer.collisionBlocksSeparation morphologyCollision

morphologyJunctionSeparatesGraphState :
  Observer.Separating morphologyJunctionObserver
morphologyJunctionSeparatesGraphState
  (Topology.graphDevelopmentalState leftMorph leftJunction)
  (Topology.graphDevelopmentalState rightMorph rightJunction)
  same
  with cong proj₁ same | cong proj₂ same
... | refl | refl = refl

morphologyJunctionIsFutureLanguageSafe :
  Future.FutureLanguageSafeProjection
    Topology.system
    Topology.morphologyProjection
    morphologyJunctionObserver
morphologyJunctionIsFutureLanguageSafe =
  FutureBridge.separatingObserverIsFutureLanguageSafe
    morphologyJunctionSeparatesGraphState

record DynamicTopologyObserverRefinementBoundary : Set where
  constructor dynamicTopologyObserverRefinementBoundary
  field
    morphologyAloneCollides : Bool
    morphologyAloneCollidesIsTrue : morphologyAloneCollides ≡ true
    junctionStrictlyRefinesMorphology : Bool
    junctionStrictlyRefinesMorphologyIsTrue :
      junctionStrictlyRefinesMorphology ≡ true
    morphologyJunctionSeparatesCurrentState : Bool
    morphologyJunctionSeparatesCurrentStateIsTrue :
      morphologyJunctionSeparatesCurrentState ≡ true
    separatingRefinementIsFutureSafeForMorphologyLanguage : Bool
    separatingRefinementIsFutureSafeForMorphologyLanguageIsTrue :
      separatingRefinementIsFutureSafeForMorphologyLanguage ≡ true

canonicalDynamicTopologyObserverRefinementBoundary :
  DynamicTopologyObserverRefinementBoundary
canonicalDynamicTopologyObserverRefinementBoundary =
  dynamicTopologyObserverRefinementBoundary
    true refl
    true refl
    true refl
    true refl
