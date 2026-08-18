module DASHI.Biology.Physical.DynamicTopologyObserverRefinementExact where

------------------------------------------------------------------------
-- DYNAMIC TOPOLOGY AS AN OBSERVER-REFINEMENT WITNESS
--
-- The existing biological example proves that equal present morphology can
-- hide a junction that changes the result of the same future signal.  Here we
-- show that adding the junction coordinate is an exact strict observer
-- refinement, and that the resulting full two-coordinate observer is safe for
-- the declared future morphology language.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Biology.Physical.DynamicTopologyFutureDefectExact as Topology
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ObserverRefinementExact as Observer

junctionProjection : Topology.GraphDevelopmentalState → Bool
junctionProjection = Topology.junction

morphologyJunctionObserver :
  Topology.GraphDevelopmentalState → Bool × Bool
morphologyJunctionObserver =
  Observer.jointObserver Topology.morphologyProjection junctionProjection

morphologyPlusJunctionStrictlyRefinesMorphology :
  Observer.StrictRefinement
    Topology.morphologyProjection
    morphologyJunctionObserver
morphologyPlusJunctionStrictlyRefinesMorphology =
  Observer.jointStrictlyRefinesWhenAddedObserverSplitsCollision
    Topology.morphologyProjection
    junctionProjection
    Topology.sameVisibleMorphology
    Topology.hiddenTopologyDiffers

morphologyProjectionCannotSeparateGraphState :
  Observer.Separating Topology.morphologyProjection → ⊥
morphologyProjectionCannotSeparateGraphState =
  Observer.strictRefinementRulesOutCoarseSeparation
    morphologyPlusJunctionStrictlyRefinesMorphology

morphologyJunctionSeparatesGraphState :
  Observer.Separating morphologyJunctionObserver
morphologyJunctionSeparatesGraphState
  {Topology.graphDevelopmentalState leftMorph leftJunction}
  {Topology.graphDevelopmentalState rightMorph rightJunction}
  same
  with cong proj₁ same | cong proj₂ same
... | refl | refl = refl

morphologyJunctionIsFutureLanguageSafe :
  Future.FutureLanguageSafeProjection
    Topology.system
    Topology.morphologyProjection
    morphologyJunctionObserver
morphologyJunctionIsFutureLanguageSafe =
  Future.futureLanguageSafeProjection λ same →
    afterSeparation (morphologyJunctionSeparatesGraphState same)
  where
    afterSeparation :
      ∀ {left right} →
      left ≡ right →
      Future.FutureObservationEquivalent
        Topology.system Topology.morphologyProjection left right
    afterSeparation {left} refl = Future.futureEquivalentRefl left

------------------------------------------------------------------------
-- Existing negative theorem remains the other side of the bridge.
------------------------------------------------------------------------

morphologyAloneStillNotFutureSafe :
  DASHI.Core.DynamicalQuotientSafety.DynamicConsumerSafety
    Topology.system Topology.morphologyProjection → ⊥
morphologyAloneStillNotFutureSafe =
  Topology.morphologyWithoutTopologyIsNotFutureSafe
